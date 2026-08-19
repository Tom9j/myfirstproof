import LinerAlgbra.chapter1_5


def CoefficientMatrix {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) :
    Ntuple (Ntuple A n) m :=
  fun row => (sys.equations row).a

def FreeCoefficientVector {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) :
    Ntuple A m :=
  fun row => (sys.equations row).b

def AugmentedMatrix {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) :
    Ntuple (Ntuple A (n + 1)) m :=
  fun row column =>
    if h : column.val < n then
      (sys.equations row).a ⟨column.val, h⟩
    else
      (sys.equations row).b
