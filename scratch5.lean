import LinerAlgbra.chapter1_1
import LinerAlgbra.Fraction

open Fraction

theorem fraction_mul_assoc : IsAssociativeOp Fraction Fraction.mul := by
  intro a b c
  unfold Fraction.mul
  congr 1
  · rw [Int.mul_assoc]
  · rw [Int.mul_assoc]

theorem fraction_add_assoc : IsAssociativeOp Fraction Fraction.add := by
  intro a b c
  unfold Fraction.add
  congr 1
  · -- goal is (a.a * b.b + b.a * a.b) * c.b + c.a * (a.b * b.b) = a.a * (b.b * c.b) + (b.a * c.b + c.a * b.b) * a.b
    -- This requires many steps of rw
    rw [Int.add_mul]
    rw [Int.add_mul]
    rw [Int.mul_assoc a.a b.b c.b]
    -- etc. We can do it!
    sorry
  · rw [Int.mul_assoc]
