package object leibniz {
  type ⊥ = Nothing
  type ⊤ = Any

  type ∀[F[_]] = Forall[F]
  type ∃[F[_]] = Exists[F]

  type ===[A, B]       = Leibniz[A, B]
  type =~=[A <: AnyKind, B <: AnyKind] = LeibnizK[A, B]

  type <~<[-A, +B] = Liskov[A, B]
  type >~>[+A, -B] = Liskov[B, A]
}
