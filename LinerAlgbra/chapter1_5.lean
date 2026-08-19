import LinerAlgbra.chapter1_4

-- Chapter 1.5: systems of linear equations

structure LinearSystem (A : Type) [Field_ A] (m n : Nat) where
  equations : Ntuple (LinearEquation A n) m


def IsSystemSolution {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n)
    (x : Ntuple A n) : Prop :=
  ∀ i : Fin m, IsSolution (sys.equations i) x
def IsHomogeneous {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) : Prop :=
  ∀ i : Fin m, (sys.equations i).b = Field_.zero


def makeHomogeneousSystem {A : Type} [Field_ A] (m n : Nat)
    (coefficients : Ntuple (Ntuple A n) m) : LinearSystem A m n :=
  { equations := fun i =>
      { a := coefficients i
        b := Field_.zero } }
