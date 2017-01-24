package leibniz

import LeibnizK.refl

//trait AnyKind

/**
  * The existence of a value of type `LeibnizK[A, B]` implies that A ≡ B,
  * regardless of the kind. For an explanation see [[Leibniz]].
  *
  * @see [[=~=]] `A =~= B` is a type synonym to `LeibnizK[A, B]`
  */
sealed abstract class LeibnizK[A <: AnyKind, B <: AnyKind] private[LeibnizK] () { ab =>
  /**
    * To create an instance of `LeibnizK[A, B]` you must show that
    * for every choice of `F[_]` you can convert `F[A]` to `F[B]`.
    */
  def subst[F[_ <: AnyKind]](fa: F[A]): F[B]

  /**
    * Substitution on identity brings about a direct coercion function.
    */
//  final def coerce(a: A)(implicit kind0: Kind0[A]): B = ???
//  {
//    type f[α[_]] = A ~> α
//    subst[f](FunctionK.id[A])
//  }

  /**
    * Equality is transitive relation and its witnesses can be composed
    * in a chain much like functions.
    *
    * @see [[compose]]
    */
  final def andThen[C <: AnyKind](bc: B =~= C): A =~= C = {
    type f[α <: AnyKind] = A =~= α
    bc.subst[f](ab)
  }

  /**
    * Equality is transitive relation and its witnesses can be composed
    * in a chain much like functions.
    *
    * @see [[andThen]]
    */
  final def compose[Z <: AnyKind](za: Z =~= A): Z =~= B =
    za.andThen(ab)

  /**
    * Equality is symmetric relation and therefore can be flipped around.
    * Flipping is its own inverse, so `x.flip.flip == x`.
    */
  final def flip: B =~= A = {
    type f[α <: AnyKind] = α =~= A
    ab.subst[f](refl[A])
  }

  /**
    * Given `A =~= B` we can prove that `F[A, ?] =~= F[B, ?]`.
    *
    * @see [[LeibnizK.lift]]
    * @see [[LeibnizK.lift2]]
    */
  final def lift[F[_ <: AnyKind] <: AnyKind]: F[A] =~= F[B] =
    LeibnizK.lift(ab)

//  /**
//    * Given `A =~= B` and `I =~= J` we can prove that
//    * `F[A, I, ?] =~= F[B, J, ?]`.
//    *
//    * @see [[LeibnizK.lift]]
//    * @see [[LeibnizK.lift2]]
//    * @see [[LeibnizK.lift3]]
//    */
//  final def lift2[F[_[_], _[_], _]]: PartiallyAppliedLift2[F] =
//    new PartiallyAppliedLift2[F]
//  final class PartiallyAppliedLift2[F[_[_], _[_], _]] {
//    def apply[I[_], J[_]](ij: I =~= J): F[A, I, ?] =~= F[B, J, ?] =
//      LeibnizK.lift2(ab, ij)
//  }
}

object LeibnizK {
  private[this] final case class Refl[A <: AnyKind]() extends LeibnizK[A, A] {
    def subst[F[_ <: AnyKind]](fa: F[A]): F[A] = fa
  }

  /**
    * Equality is reflexive relation.
    */
  def refl[A <: AnyKind]: A =~= A = Refl[A]()

  /**
    * Given `A =~= B` we can prove that `F[A, ?] =~= F[B, ?]`.
    *
    * @see [[lift2]]
    * @see [[lift3]]
    */
  def lift[F[_ <: AnyKind] <: AnyKind, A <: AnyKind, B <: AnyKind]
  (ab: A =~= B): F[A] =~= F[B] = {
    type f[α <: AnyKind] = F[A] =~= F[α]
    ab.subst[f](refl[F[A]])
  }

//  /**
//    * Given `A =~= B` and `I =~= J` we can prove that
//    * `F[A, I, ?] =~= F[B, J, ?]`.
//    *
//    * @see [[lift]]
//    * @see [[lift3]]
//    */
//  def lift2[F[_[_], _[_], _], A[_], B[_], I[_], J[_]]
//  (ab: A =~= B, ij: I =~= J): F[A, I, ?] =~= F[B, J, ?] = {
//    type f1[α[_]] = F[A, I, ?] =~= F[α, I, ?]
//    type f2[α[_]] = F[A, I, ?] =~= F[B, α, ?]
//    ij.subst[f2](ab.subst[f1](refl[F[A, I, ?]]))
//  }
//
//  /**
//    * Given `A =~= B`, `I =~= J`, and `M =~= N` we can prove that
//    * `F[A, I, ?] =~= F[B, J, ?]`.
//    *
//    * @see [[lift]]
//    * @see [[lift2]]
//    */
//  def lift3[F[_[_], _[_], _[_], _], A[_], B[_], I[_], J[_], M[_], N[_]]
//  (ab: A =~= B, ij: I =~= J, mn: M =~= N): F[A, I, M, ?] =~= F[B, J, N, ?] = {
//    type f1[α[_]] = F[A, I, M, ?] =~= F[α, I, M, ?]
//    type f2[α[_]] = F[A, I, M, ?] =~= F[B, α, M, ?]
//    type f3[α[_]] = F[A, I, M, ?] =~= F[B, J, α, ?]
//    mn.subst[f3](ij.subst[f2](ab.subst[f1](refl[F[A, I, M, ?]])))
//  }
}