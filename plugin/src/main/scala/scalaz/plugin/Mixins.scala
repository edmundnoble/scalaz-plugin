package scalaz.plugin

import scala.collection.mutable
import scala.tools.nsc.ast.TreeBrowsers
import scala.tools.nsc.transform.{Transform, TypingTransformers}
import scala.tools.nsc.typechecker.AnalyzerPlugins
import scala.tools.nsc.{Global, Phase, plugins}
import scala.util.control.NonFatal
import miniz._

/**
  * Mixins is responsible for expanding type class definitions in datatype companion objects,
  * to duplicate code from superclass instances to subclass instances.
  *
  * It duplicates code *verbatim*, in a way which aims to be almost textual; code is essentially
  * copy-pasted between instances. If it wouldn't typecheck if you copied and pasted it yourself,
  * mixins will not fix that.
  *
  * To do this, it requires some things from the user:
  *   - Type class instances *MUST* be coherent and globally unique, or this transformation doesn't even make sense
  *     because the question of "which code should I copy" is fundamentally unanswerable and must be decided fully
  *     by the user.
  *   - Type class instances must be topologically sorted inside of companion objects.
  *     i.e. Superclass instances must occur before subclass instances.
  *     This avoids requiring multiple passes inside of the plugin, allowing it to track
  *     limited state.
  *   - Type class instances must contain no methods other than those inside of the type class
  *     interface itself.
  *     This means we're able to use `@minimal` annotations to determine how much code needs to be copied,
  *     so we don't need to introspect methods to see how many "hidden" methods are called (that would also need to be copied),
  *     *especially* because extra methods are usually used to hide state, and copying state can be *very bad* for users.
  *   - Type class methods must be uniquely named *across type classes*. With this in mind, mixins can be viewed as a method resolution and copying
  *     mechanism, without reference to the classes themselves.
  *   - Type classes must be uniquely named. This might not be required by the plugin necessarily,
  *     I haven't tried to use conflicting type class names but it's not likely to work.
  *
  */
//   -
//
abstract class Mixins extends plugins.PluginComponent with Utils {
  val global: Global
  val scalazDefns: Definitions { val global: Mixins.this.global.type }

  val mixinPlugin = new global.analyzer.MacroPlugin {
    override def isActive(): Boolean =
      global.phase.id < global.currentRun.picklerPhase.id

    case class TypeClassInstance(implementedMethods: Map[String, global.ValOrDefDef],
                                 instanceTy: global.Type,
                                 tyParamSyms: TyParamSubstMap,
                                 valueParamSyms: ValueParamSubstMap,
                                 oldAnonClass: global.Symbol)

    def substituteInstanceMethods(methods: Map[String, global.ValOrDefDef])
                                 (tyParamSyms: TyParamSubstMap,
                                  valueParamSyms: ValueParamSubstMap,
                                  oldAnonClass: global.Symbol)
                                 (newTyParamSyms: TyParamSubstMap,
                                  newValueParamSyms: ValueParamSubstMap,
                                  newAnonClass: global.Symbol): Map[String, global.ValOrDefDef] = {
      val (oldTys, newTys) = tyParamSyms.map {
        case (k, v) =>
          newTyParamSyms.get(k).map(ns => (v.newTypeSkolem, ns.newTypeSkolem))
      }.toList.flatten.unzip
      val (oldVs, newVs) = valueParamSyms.map {
        case (k, v) =>
          newValueParamSyms.get(k).map(ns => (v, ns))
      }.toList.flatten.unzip
      methods.mapValues { b =>
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

    val extractInstanceTypeFromDeclType
      : global.Type => (global.Type, TyParamSubstMap, ValueParamSubstMap) = {
      case pt @ global.PolyType(_, methTy: global.MethodType) =>
        println("poly")
        val tyParamsMap    = pt.params.map(p => (p.name.toString, p)).toMap
        val valueParamsMap = methTy.params.map(p => (p.name.toString, p)).toMap
        (methTy.resultType, tyParamsMap, valueParamsMap)
      case pt @ global.PolyType(_, nmt: global.NullaryMethodType) =>
        println("poly")
        val tyParamsMap    = pt.params.map(p => (p.name.toString, p)).toMap
        (nmt.resultType, tyParamsMap, Map.empty)
      case methTy: global.MethodType =>
        println("meth")
        val valueParamsMap = methTy.params.map(p => (p.name.toString, p)).toMap
        (methTy.resultType, Map.empty, valueParamsMap)
      case nme: global.NullaryMethodType =>
        println("nme")
        (nme.resultType, Map.empty, Map.empty)
      case ty =>
        println(s"nei: ${ty.getClass}")
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

    @inline def tupleR[A, B](self: A)(f: A => B): (B, A) = (f(self), self)
    @inline def tuple[A, B](fst: A, snd: B): (A, B) = (fst, snd)
    @inline def methodName(t: global.ValOrDefDef): String = t.name.toString
    @inline def typeName(t: global.Type): String = t.typeSymbol.name.toString

    def getExtraCode(instance: TypeClassInstance, otherInstances: Iterator[TypeClassInstance]): Map[String, global.ValOrDefDef] = {
      val scs = findSuperclasses(instance.instanceTy)
      val scsNames = scs.iterator.map(typeName).toSet
      val scInstances: Iterator[TypeClassInstance] = otherInstances.filter {
            // fuck, deal with intersection types as refinements somehow
        i => println(s"tn: ${typeName(i.instanceTy.isStructuralRefinement)}"); scsNames(typeName(i.instanceTy))
      }
      println(s"scInstances: $scInstances")
      println(s"scsNames: $scsNames")
      // deliberately not tail-recursive.
      def implementClasses(cls: Iterator[TypeClassInstance]): Map[String, global.ValOrDefDef] =
        if (cls.hasNext) {
          val nextInstance = cls.next()
          println(s"nextInstance: $nextInstance")

          val methodsToCopy = findSuperclasses(nextInstance.instanceTy).iterator
            .filter(c => scsNames(typeName(c)))
            .flatMap(k => minimalNames(k.typeSymbol).fold(k.decls.map(_.name.toString).toSet)(_.methods.flatten.toSet))
            .toSet
          println(s"methodsToCopy: $methodsToCopy")

          val substMeths =
            substituteInstanceMethods(nextInstance.implementedMethods.filterKeys(methodsToCopy))(
              // from
              nextInstance.tyParamSyms, nextInstance.valueParamSyms, nextInstance.oldAnonClass
            )(
              // to
              instance.tyParamSyms, instance.valueParamSyms, instance.oldAnonClass
            )
          println(s"substMeths: $substMeths")
          // methods implemented "later" supersede the earlier ones.
          substMeths ++ implementClasses(cls)
        } else {
          Map.empty
        }
      implementClasses(scInstances)
    }

    def grabDefs(ls: List[global.Tree]): List[global.ValOrDefDef] = ls.collect {
      case d: global.ValOrDefDef => d
    }

    case class Minimal(methods: List[Set[String]])

    def minimalNames(sym: global.Symbol): Option[Minimal] =
      sym.getAnnotation(scalazDefns.MinimalAttr).map(minimalNames)

    def minimalNames(ann: global.AnnotationInfo): Minimal = {
      def isTupleApply(s: global.Symbol): Boolean =
        s.isMethod && global.definitions.isTupleSymbol(s.owner.companion)

      ann.tree match {
        case global.treeInfo.Applied(global.Select(global.New(_), _), _, args :: Nil) =>
          Minimal(args.map {
            case global.Literal(global.Constant(name: String)) =>
              Set(name)
            case global.Apply(fun, args) if isTupleApply(fun.symbol) =>
              args.iterator.map {
                case global.Literal(global.Constant(name: String)) =>
                  name
              }.toSet
          })
      }
    }

    // tests for the absence and presence of multiple symbols at once inside a tree
    def treeContainsSyms(tree: global.Tree, strs: List[global.TermName]): Map[global.TermName, Boolean] = {
      val strsSet = strs.toSet
      val strsState = mutable.Map.empty[global.TermName, Boolean]
      tree.foreach {
        case global.Ident(s: global.TermName) =>
          if (strsSet(s)) {
            strsState += s -> true
          }
        case _ => ()
      }
      strsState.toMap
    }

    def transformInstanceDefn(
       state: mutable.ListBuffer[TypeClassInstance],
       typer: global.analyzer.Typer,
       defn: global.ValOrDefDef
    ): Either[LocatedError, global.ValOrDefDef] =
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
        _ = println(s"defn.symbol: ${defn.symbol}")
        _ = println(s"instanceTy: $instanceTy")
        _ <- instanceTy match {
          case _: global.NoType.type =>
            Left(
              "Type class instance definition wasn't type checked? Report this as a bug."
                .errorAt(defn.pos)
            )
          case _ => Right(())
        }
        // What if the instance implements methods from super classes?
        allImplementedMethods = removeInit(grabDefs(anonClass.impl.body))
        missingMethods = (instanceTy.decls.iterator.filterNot(_.isOverridingSymbol).map(_.name.toString).toSet -- allImplementedMethods.map(_.name.toString)).iterator.filterNot(isInit).mkString(", ")
        _ <- if (missingMethods.nonEmpty) {
          println(s"missing methods: $missingMethods")
          Left(s"Type class instance definition does not implement some required methods: $missingMethods".errorAt(anonClass.pos))
        } else {
          Right(())
        }
        _ = println(s"WTF 1: ${removeInit(grabDefs(anonClass.impl.body))}")
        newInstance = TypeClassInstance(
          allImplementedMethods.iterator.map(tupleR(_)(_.name.toString)).toMap,
          instanceTy,
          tySubstMap,
          valSubstMap,
          anonClass.symbol
        )
        extraCode =
          getExtraCode(newInstance, state.iterator)
        _ = println(extraCode)
        // this can't work right now.
//        _ <- if (state.exists(i => (i.implementedMethods.keySet & allImplementedClasses.iterator.map(_._2.decls).filter(_.nonEmpty).toSet).nonEmpty)) {
//          Left(
//            "Only one instance in an @instances object is allowed per type class."
//              .errorAt(defn.pos)
//          )
//        } else {
        _ = state += newInstance
//          Right(())
//        }
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
        newTree <- extraCode.valuesIterator.toList match {
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
          .map(original => expandTree(state, typer, original).map(tuple(original, _)))
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
      } else stats

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
