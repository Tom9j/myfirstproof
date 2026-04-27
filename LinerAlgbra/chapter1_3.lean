import LinerAlgbra.chapter1_2

def NTuple (A : Type) (n : Nat) := Fin n → A

def NTuple_Equal {A : Type} {n : Nat} (u v : NTuple A n) : Prop :=
  ∀ i, u i = v i

def NTuple_add {A : Type} [Field_ A] {n : Nat} : Operation (NTuple A n) (NTuple A n) (NTuple A n) :=
  fun u v => fun i => Field_.add (u i) (v i)



def NTuple_smul {A : Type} [Field_ A] {n : Nat} : Operation A (NTuple A n) (NTuple A n) :=
  fun c v => fun i => Field_.mul c (v i)
