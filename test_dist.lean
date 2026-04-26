import Mathlib

def Operation (A : Type) : Type := A ? A ? A
def IsDistributiveFromLeft (A:Type) (op1 : Operation A) (op2 : Operation A) : Prop := ? a b c : A, op1 a (op2 b c) = op2 (op1 a b) (op1 a c)
def IsDistributiveFromRight (A:Type) (op1 : Operation A) (op2 : Operation A) : Prop := ? a b c : A, op1 (op2 a b) c = op2 (op1 a c) (op1 b c)
def IsDistributive (A:Type) (op1 : Operation A) (op2 : Operation A) : Prop := IsDistributiveFromLeft A op1 op2 ? IsDistributiveFromRight A op1 op2

example : IsDistributive R (fun x y => x * y) (fun x y => x + y) := by
  constructor
  · intro a b c
    exact mul_add a b c
  · intro a b c
    exact add_mul a b c
