import LinerAlgbra.chapter1_1
import LinerAlgbra.Fraction

open Fraction

theorem fraction_mul_assoc : IsAssociativeOp Fraction Fraction.mul := by
  intro a b c
  unfold Fraction.mul
  dsimp
  congr 1
  · exact Int.mul_assoc a.a b.a c.a
  · exact Int.mul_assoc a.b b.b c.b
