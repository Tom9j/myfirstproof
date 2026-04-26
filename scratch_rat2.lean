import LinerAlgbra.chapter1_1

theorem rat_mul_1_Netural : IsNeutralElement ℚ (· * ·) 1 := by
  intro a
  apply And.intro
  · exact one_mul a
  · exact mul_one a

-- במקום AllElementsHaveInverse, נצטרך להוכיח שכל איבר שונה מאפס הוא הפיך
theorem rat_mul_inverse_nonzero (a : ℚ) (ha : a ≠ 0) : IsInverseElement ℚ (· * ·) 1 rat_mul_1_Netural a := by
  use a⁻¹
  apply And.intro
  · exact mul_inv_cancel₀ ha
  · exact inv_mul_cancel₀ ha
