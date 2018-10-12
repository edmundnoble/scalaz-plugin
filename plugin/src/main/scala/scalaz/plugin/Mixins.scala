package scalaz.plugin

import scala.collection.mutable
import scala.tools.nsc.ast.TreeBrowsers
import scala.tools.nsc.transform.{Transform, TypingTransformers}
import scala.tools.nsc.typechecker.AnalyzerPlugins
import scala.tools.nsc.{Global, Phase, plugins}
import scala.util.control.NonFatal
import miniz._

abstract class Mixins extends plugins.PluginComponent with Utils {
  val global: Global
  val scalazDefns: Definitions { val global: Mixins.this.global.type }

  val mixinPlugin = new global.analyzer.MacroPlugin {
    override def isActive(): Boolean =
      global.phase.id < global.currentRun.picklerPhase.id

    // this is a bit broken. If we have a map from implemented class to `global.Tree`, or rather to `StatePart`,
    // we can avoid copying redundant methods.
    // to do so we'd have to remove methods that belong to other classes...
    // unless they're referenced by other methods inside the subclass?
    // hmmmmmm.
    case class TypeClassInstance(implementedClasses: Map[String, global.Type],
                                 body: List[global.ValOrDefDef],
                                 tyParamSyms: TyParamSubstMap,
                                 valueParamSyms: ValueParamSubstMap,
                                 oldAnonClass: global.Symbol) {
    }

    def substituteInstanceMethods(methods: Iterator[global.ValOrDefDef])
                                 (tyParamSyms: TyParamSubstMap,
                                  valueParamSyms: ValueParamSubstMap,
                                  oldAnonClass: global.Symbol)
                                 (newTyParamSyms: TyParamSubstMap,
                                  newValueParamSyms: ValueParamSubstMap,
                                  newAnonClass: global.Symbol): Iterator[global.ValOrDefDef] = {
      val (oldTys, newTys) = tyParamSyms.map {
        case (k, v) =>
          newTyParamSyms.get(k).map(ns => (v.newTypeSkolem, ns.newTypeSkolem))
      }.toList.flatten.unzip
      val (oldVs, newVs) = valueParamSyms.map {
        case (k, v) =>
          newValueParamSyms.get(k).map(ns => (v, ns))
      }.toList.flatten.unzip
      methods.map { b =>
        // substituteSymbols mutates the tree in place
        println(s"TRYIN: $b")
        val n = b.duplicate
          .substituteSymbols(
            oldVs ++ oldTys ++ List(oldAnonClass),
            newVs ++ newTys ++ List(newAnonClass)
          )
          .changeOwner(oldAnonClass -> newAnonClass)
          .asInstanceOf[global.ValOrDefDef]
        println(s"WOO: $n")
        n
      }
    }

    type TyParamSubstMap    = Map[String, global.Symbol]
    type ValueParamSubstMap = Map[String, global.Symbol]

    def isInstanceDefn(defn: global.ValOrDefDef): Boolean = {
      // the last case is required to find backing `val`s
      val realResultType = defn.symbol.info match {
        case global.PolyType(_, methTy: global.MethodType) => methTy.resultType
        case methTy: global.MethodType                     => methTy.resultType
        case ty                                            => ty
      }
      val isTypeClassType =
        realResultType.baseTypeSeq.toList.contains[global.Type](scalazDefns.TypeclassType)
      val isUnmixin = defn.symbol.hasAnnotation(scalazDefns.UnmixinAttr)
      isTypeClassType && !isUnmixin
    }

    def instanceDefn: global.Tree => Option[global.ValOrDefDef] = _.opt {
      case defn: global.ValOrDefDef if isInstanceDefn(defn) =>
        defn
    }

    def extractInstanceParts(defn: global.ValOrDefDef): Option[(global.ClassDef, global.Tree)] =
      defn.rhs.opt {
        case global.Block(List(cld: global.ClassDef), instantiation) =>
          (cld, instantiation)
      }

    def extractInstanceTypeFromDeclType
      : global.Type => (global.Type, TyParamSubstMap, ValueParamSubstMap) = {
      case pt @ global.PolyType(_, methTy: global.MethodType) =>
        val tyParamsMap    = pt.params.map(p => (p.name.toString, p)).toMap
        val valueParamsMap = methTy.params.map(p => (p.name.toString, p)).toMap
        (methTy.resultType, tyParamsMap, valueParamsMap)
      case methTy: global.MethodType =>
        val valueParamsMap = methTy.params.map(p => (p.name.toString, p)).toMap
        (methTy.resultType, Map.empty, valueParamsMap)
      case nme: global.NullaryMethodType =>
        (nme.resultType, Map.empty, Map.empty)
      case ty =>
        (ty, Map.empty, Map.empty)
    }

    def findSuperclasses(tpe: global.Type): List[global.Type] =
      tpe.baseTypeSeq.toList.filterNot { ty =>
        ty == tpe ||
        ty == global.definitions.AnyTpe ||
        ty == global.definitions.AnyRefTpe ||
        ty == global.definitions.ObjectTpe ||
        ty == global.definitions.SerializableTpe ||
        ty == scalazDefns.TypeclassType
      }

    def listTraverseOption[A, B](list: List[A])(f: A => Option[B]): Option[List[B]] =
      list.foldRight[Option[List[B]]](Some(Nil)) {
        case (a, bso) => f(a).flatMap(b => bso.map(b :: _))
      }

    def removeInit(stats: List[global.ValOrDefDef]): List[global.ValOrDefDef] =
      stats.filter { d =>
        val nameStr = d.name.toString
        !isInit(nameStr)
      }

    def isInit(str: String): Boolean = {
      str == "<init>" || str == "$init$"
    }

    def tupleR[A, B](self: A)(f: A => B): (B, A) = (f(self), self)

    def implementedClasses(anonClass: global.ClassDef, instanceTy: global.Type, superclasses: List[global.Type]): Either[LocatedError, (Map[String, global.Type], Map[String, global.Type])] = {
      val anonDefns = removeInit(grabDefs(anonClass.impl.body))

      def findImplementedClasses(sofar: Map[String, global.Type], methods: Set[String], otherSuperclasses: List[global.Type]): (Map[String, global.Type], Map[String, global.Type]) =
        if (methods.isEmpty || otherSuperclasses.isEmpty) {
          val zeroMethodSuperclasses = otherSuperclasses.iterator.filter(_.decls.isEmpty).map(tupleR(_)(_.typeSymbol.name.toString)).toMap
          val unimplemented = otherSuperclasses.iterator.filterNot(_.decls.isEmpty).map(tupleR(_)(_.typeSymbol.name.toString)).toMap
          (sofar ++ zeroMethodSuperclasses, unimplemented)
        } else {
          println(s"methods: ${methods}")
          val nextSuperclass = otherSuperclasses.head
          println(s"nextSuperclass: ${nextSuperclass}")
          val nextSuperclassDecls = nextSuperclass.decls.map(_.name.toString).toSet
          println(s"nextSuperclassDecls: ${nextSuperclassDecls}")
          if (nextSuperclassDecls.subsetOf(methods)) {
            println(s"new methods: ${methods -- nextSuperclassDecls}")
            findImplementedClasses(
              sofar + (nextSuperclass.typeSymbol.name.toString -> nextSuperclass),
              methods -- nextSuperclassDecls,
              otherSuperclasses.tail
            )
          } else {
            // we have more methods, but none are from this type class.
            findImplementedClasses(sofar, methods, otherSuperclasses.tail)
          }
        }
      val allMethodNames = anonDefns.map(_.name.toString).toSet
      val (implemented, notImplemented) = findImplementedClasses(Map.empty, allMethodNames, instanceTy :: superclasses)
      println(s"start defns: ${anonDefns}")
      println(s"Superclasses: ${superclasses}")
      println(s"Implemented superclasses: ${implemented}")
      if (implemented.isEmpty) {
        val missingMethods = (instanceTy.decls.iterator.map(_.name.toString).toSet -- allMethodNames).filterNot(isInit).mkString(", ")
        println(s"missing methods: ${missingMethods}")
        Left(s"Type class instance definition does not implement some required methods: $missingMethods".errorAt(anonClass.pos))
      } else {
        Right((implemented, notImplemented))
      }
    }

    def findExtraCode(tc: TypeClassInstance,
                      notImplemented: Map[String, global.Type],
                      state: Iterator[TypeClassInstance]): Either[LocatedError, List[global.Tree]] = {
      // i.e., there are no superclasses.
      if (tc.implementedClasses.size < 2) Right(Nil)
      else {
        var classCursor = notImplemented
        val allExtraCode = List.newBuilder[global.ValOrDefDef]
        while (state.hasNext && classCursor.nonEmpty) {
          val nextInstance = state.next()
          val shared = classCursor.keySet.intersect(nextInstance.implementedClasses.keySet)
          println(s"next: ${nextInstance}")
          println(s"shared: ${shared}")
          println(s"curs: ${classCursor}")
          if (shared.nonEmpty) {
            classCursor --= shared
            println(s"curs new: ${classCursor}")
            // go through `nextInstance.body`, adding things that reference `copiedMethods` to `copiedMethods`.
            // keep iterating until you get no new methods.
            // restart with that thing added to `rootCopiedMethods`.
            // *then* substitute on all of the copied methods.
            // optimization: should remove `rootCopiedMethods` from `nextInstance.body` copy first.
            val allMethods = nextInstance.body
            println(s"all meths: ${allMethods}")
            val allMethodsByName: Map[String, global.ValOrDefDef] =
              allMethods.iterator.map(tupleR(_)(_.name.toString)).toMap
            println(s"all methsbyname: ${allMethodsByName}")
            val rootCopiedMethodsByName: Map[String, global.ValOrDefDef] =
              shared.iterator.flatMap(nextInstance.implementedClasses(_).decls.flatMap { s =>
                val n = s.name.toString
                allMethodsByName.get(n).map(l => (n, l))
              }).toMap
            println(s"root methsbyname: ${rootCopiedMethodsByName}")
            // perhaps needs to be optimized.
            // finds all methods in the new instance body that reference the set `sofar`,
            // adds them to `sofar`. A kind of closure operator.
            @scala.annotation.tailrec def getCopiedMethods(sofar: Map[String, global.ValOrDefDef]): Map[String, global.ValOrDefDef] = {
              val newMethods = allMethodsByName.filter {
                case (_, v) => v.hasSymbolWhich(c => sofar.contains(c.name.toString))
              } ++ rootCopiedMethodsByName
              println(s"new methods: ${newMethods}")
              if (newMethods.keySet != sofar.keySet) {
                getCopiedMethods(newMethods)
              } else {
                sofar
              }
            }

            val newMeths = getCopiedMethods(rootCopiedMethodsByName).valuesIterator
            println(s"all new methods: ${newMeths}")

            val substMeths =
              substituteInstanceMethods(newMeths)(
                nextInstance.tyParamSyms, nextInstance.valueParamSyms, nextInstance.oldAnonClass)(
                tc.tyParamSyms, tc.valueParamSyms, tc.oldAnonClass
              )
            println(s"all subst methods: ${substMeths}")

            allExtraCode ++= substMeths

          }
        }
        if (classCursor.nonEmpty) {
          Left(s"Some superclasses are not implemented: ${classCursor.valuesIterator.mkString(", ")}".errorAt(tc.oldAnonClass.pos))
        } else {
          Right(allExtraCode.result())
        }
      }
    }

    def grabDefs(ls: List[global.Tree]): List[global.ValOrDefDef] = ls.collect {
      case d: global.ValOrDefDef => d
    }

    def transformInstanceDefn(
                               state: mutable.ListBuffer[TypeClassInstance],
                               typer: global.analyzer.Typer,
                               defn: global.ValOrDefDef
                             ): Either[LocatedError, global.ValOrDefDef] = {
      for {
        t <- extractInstanceParts(defn).orError(
          "Type class instance definition is only allowed to contain `new InstanceType {<body>}`"
            .errorAt(defn.pos)
        )
        (anonClass, newCall) = t
        // only safe once we know that `defn` is really a `DefDef` or `ValDef`
        (instanceTy, tySubstMap, valSubstMap) = extractInstanceTypeFromDeclType(
          defn.symbol.info
        )
        _ <- instanceTy match {
          case _: global.NoType.type =>
            Left(
              "Type class instance definition wasn't type checked? Report this as a bug."
                .errorAt(defn.pos)
            )
          case _ => Right(())
        }
        scs = findSuperclasses(instanceTy)
        // What if the instance implements methods from super classes?
        t2 <- implementedClasses(anonClass, instanceTy, scs)
        (allImplementedClasses, notImplementedClasses) = t2
        _ = println(s"WTF 1: ${removeInit(grabDefs(anonClass.impl.body))}")
        newInstance = TypeClassInstance(allImplementedClasses, removeInit(grabDefs(anonClass.impl.body)), tySubstMap, valSubstMap, anonClass.symbol)
        extraCode <- findExtraCode(newInstance, notImplementedClasses, state.iterator)
        _ = println(extraCode)
        _ <- if (state.exists(i => (i.implementedClasses.filter(_._2.decls.nonEmpty).keySet & allImplementedClasses.filter(_._2.decls.nonEmpty).keySet).nonEmpty)) {
          Left(
            "Only one instance in an @instances object is allowed per type class."
              .errorAt(defn.pos)
          )
        } else {
          state += newInstance
          Right(())
        }
        _ = println("WTF")
//        _ <- if (state.contains(instanceTy.typeSymbol.name.toString)) {
//        } else {
//          state += (instanceTy.typeSymbol.name.toString -> StatePart(
//            removeInit(anonClass.impl.body),
//            tySubstMap,
//            valSubstMap,
//            anonClass.symbol
//          ))
//          Right(())
//        }
//        extraCode = listTraverseOption(scs)(t => state.get(t.typeSymbol.name.toString)).map {
//          _.flatMap(_.substitute(tySubstMap, valSubstMap, anonClass.symbol))
//        }
        newTree <- extraCode match {
            // this is semantically necessary so that we only unlink and relink symbols when it makes sense.
          case Nil => Right(defn)
          case code =>
            val newBody = global
              .Block(
                List(
                  global.deriveClassDef(
                    anonClass
                  )(_.copy(body = anonClass.impl.body ++ code))
                ),
                newCall
              )
              .duplicate
            if (defn.isInstanceOf[global.DefDef])
              Right(global.deriveDefDef(defn)(_ => newBody))
            else
              Right(global.deriveValDef(defn)(_ => newBody))
//          case None =>
//            val missingClasses = scs
//              .map(_.typeSymbol.name.toString)
//              .toSet -- state.keySet
//            Left(
//              s"A type class instance is missing instances of its parent classes: ${missingClasses
//                .mkString(",")}".errorAt(defn.pos)
//            )
        }
      } yield newTree
    }

    def expandTree(state: mutable.ListBuffer[TypeClassInstance],
                   typer: global.analyzer.Typer,
                   tr: global.Tree): Either[LocatedError, global.Tree] =
      instanceDefn(tr) match {
        case None =>
          println("no instance defn!")
          Right(tr)
        case Some(defn) =>
          println(s"instance defn! $defn")
          transformInstanceDefn(state, typer, defn)
      }

    override def pluginsEnterStats(typer: global.analyzer.Typer,
                                   stats: List[global.Tree]): List[global.Tree] =
      if (typer.context.owner.hasAnnotation(scalazDefns.InstancesAttr)) {
        val state: mutable.ListBuffer[TypeClassInstance] = mutable.ListBuffer.empty
        stats
          .map{original => println(original); expandTree(state, typer, original).map(n => (original, n))}
          .uncozip
          .fold(
            { es =>
              es.foreach {
                case LocatedError(pos, msg) =>
                  global.reporter.error(pos, msg)
              }
              stats
            }, { ts =>
              ts.foreach {
                case (o, n) =>
                  if (o ne n) {
                    typer.context.owner.info.decls.unlink(o.symbol)
                    typer.namer.enterSym(n)
                  }
                  n
              }; ts.map(_._2)
            }
          )
      } else {
        stats
      }

  }

  global.analyzer.addMacroPlugin(mixinPlugin)

  import global._, scalazDefns.{ global => _, _ }

  override val phaseName: String        = "scalaz-mixins"
  override val runsAfter: List[String]  = "namer" :: Nil
  override val runsBefore: List[String] = "superaccessors" :: Nil

  override def newPhase(prev: scala.tools.nsc.Phase): StdPhase = new StdPhase(prev) {
    def apply(unit: global.CompilationUnit): Unit = ()
  }
}
