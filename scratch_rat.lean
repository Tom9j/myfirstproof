import LinerAlgbra.chapter1_1

-- חוק הפילוג של כפל מעל חיבור עבור רציונליים (ℚ)
theorem rat_mul_add_Distributive : IsDistributive ℚ (· * ·) (· + ·) := by
  apply And.intro
  · intro a b c
    exact mul_add a b c
  · intro a b c
    exact add_mul b c a

theorem rat_add_0_Netural : IsNeutralElement ℚ (· + ·) 0 := by
  intro a
  apply And.intro
  · exact zero_add a
  · exact add_zero a

theorem rat_add_inverse : AllElementsHaveInverse ℚ (· + ·) 0 rat_add_0_Netural := by
  intro a
  use -a
  apply And.intro
  · exact add_neg_cancel a
  · exact neg_add_cancel a
