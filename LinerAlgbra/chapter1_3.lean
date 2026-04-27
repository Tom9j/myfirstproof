import LinerAlgbra.chapter1_2

def NTuple (A : Type) (n : Nat) := Fin n → A

def NTuple_Equal {A : Type} {n : Nat} (u v : NTuple A n) : Prop :=
  ∀ i, u i = v i
