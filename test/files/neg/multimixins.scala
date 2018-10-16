import scalaz.meta.{instances, orphan, Typeclass}

trait Marker extends Typeclass {
}

trait Semigroup[A] extends Marker {
  def mappend(fst: A, snd: A): A
}

trait Monoid[A] extends Semigroup[A] {
  def mempty: A
}

trait CommutativeMonoid[A] extends Monoid[A]

trait Band[A] extends Monoid[A]

trait Semilattice[A] extends Band[A] with CommutativeMonoid[A]

trait Invariant[F[_]] extends Typeclass {
  def xmap[A, B](to: A => B, from: B => A)(fa: F[A]): F[B]
}

trait Contravariant[F[_]] extends Invariant[F] {
  def contramap[A, B](from: B => A)(fa: F[A]): F[B]
  override def xmap[A, B](to: A => B, from: B => A)(fa: F[A]): F[B] = contramap[A, B](from)(fa)
}

trait Functor[F[_]] extends Invariant[F] {
  def map[A, B](to: A => B)(fa: F[A]): F[B]
  override def xmap[A, B](to: A => B, from: B => A)(fa: F[A]): F[B] = map[A, B](to)(fa)
}

trait Apply[F[_]] extends Functor[F] {
  def ap[A, B](ff: F[A => B])(fa: F[A]): F[B]
}

//case class Identity[A](a: A)
//
//@instances object Identity {
////  implicit def monoid[A](implicit A: Monoid[A]): Monoid[Identity[A]] = new Monoid[Identity[A]] {
////    def mappend(fst: Identity[A], snd: Identity[A]): Identity[A] = Identity(A.mappend(fst.a, snd.a))
////    def mempty: Identity[A] = Identity[A](A.mempty)
////  }
////
////  implicit def semilattice[A](implicit A: Semilattice[A]): Semilattice[Identity[A]] =
////    new Semilattice[Identity[A]] {}
//
//  implicit def functor: Functor[Identity] = new Functor[Identity] {
//    def map[A, B](atb: A => B)(fa: Identity[A]): Identity[B] = Identity(atb(fa.a))
//  }
//
//}
//
//case class Const[A, B](a: A)
//
//@instances object Const {
//  type C[A] = {type l[B] = Const[A, B]}
//  def functor[X]: Functor[C[X]#l] = new Functor[C[X]#l] {
//    def map[A, B](to: A => B)(fa: Const[X, A]): Const[X, B] = Const(fa.a)
//  }
//}

case class Const2[A, B](a: A)

@instances object Const2 {
  type C[A] = {type l[B] = Const2[A, B]}
  implicit def fInstance[X]: Functor[C[X]#l] with Contravariant[C[X]#l] =
    new Functor[C[X]#l] with Contravariant[C[X]#l] {
      def map[A, B](to: A => B)(fa: Const2[X, A]): Const2[X, B] = Const2(fa.a)
      def contramap[A, B](from: B => A)(fa: Const2[X, A]): Const2[X, B] = Const2(fa.a)
    }

  implicit def aInstance[X]: Apply[C[X]#l] =
    new Apply[C[X]#l] {
      def ap[A, B](ff: Const2[X, A => B])(fa: Const2[X, A]): Const2[X, B] = Const2(fa.a)
    }
}

// test when instance defns have more than new Instance {}

// test when instance defns are missing methods that they need

// test when instance defns explicitly override methods from superclasses

// test when an instance defn has superclasses with no methods

// test when an instance defn has type aliases in the class name

// test when an instance defn has type aliases in the type name

// test when *multiple* instance defns have superclasses with no methods

// test implementing a type class with default implementations of superclass methods

// test the case where you have an instance of Functor and an instance of Contravariant
// (both have *conflicting* default impls of `xmap` from Invariant)

// test the case where copied methods call superclass methods that aren't needed to implement the current instance

// test the case where copied methods call non-superclass methods that aren't needed to implement the current instance

