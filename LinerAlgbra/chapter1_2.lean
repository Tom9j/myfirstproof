import LinerAlgbra.chapter1_1

class Field_ (A : Type) where
  -- איברים ופעולות (נניח ש-Operation מוגדר כ- A → A → A)
  zero : A
  one : A
  add : Operation A
  mul : Operation A

  -- הנחות על חיבור באמצעות ההגדרות שלך
  add_closed : IsClosedOp A add
  add_assoc  : IsAssociativeOp A add
  add_comm   : IsCommutativeOp A add
  add_neut   : IsNeutralElement A add zero
  add_inv    : AllElementsHaveInverse A add zero add_neut -- Lean מאפשר להשתמש בשורה הקודמת!

  -- הנחות על כפל באמצעות ההגדרות שלך
  mul_closed : IsClosedOp A mul
  mul_assoc  : IsAssociativeOp A mul
  mul_comm   : IsCommutativeOp A mul
  mul_neut   : IsNeutralElement A mul one

  -- הופכי לכפל: נכתוב את התנאי ישירות כדי לדלג על ה-zero
  mul_inv    : ∀ a : A, a ≠ zero → ∃ b : A, mul a b = one ∧ mul b a = one

  -- פילוג
  distribLeft    : IsDistributiveFromLeft A mul add

  -- שונה מאפס
  zero_neq_one : zero ≠ one

instance : Field_ Rat where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)

  add_closed := rat_add_closed
  add_assoc  := rat_add_assoc
  add_comm   := rat_add_Commutative
  add_neut   := rat_add_0_Netural
  add_inv    := rat_add_inverse

  mul_closed := rat_mul_closed
  mul_assoc  := rat_mul_assoc
  mul_comm   := rat_mul_Commutative
  mul_neut   := rat_mul_1_Netural
  mul_inv    := rat_mul_inverse_nonzero
  distribLeft := rat_mul_add_Distributive.left
  zero_neq_one := rat_zero_neq_one



instance : Field_ ℝ where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)

  add_closed := real_add_closed
  add_assoc  := real_add_assoc
  add_comm   := real_add_Commutative
  add_neut   := real_add_0_Netural
  add_inv    := real_add_inverse

  mul_closed := real_mul_closed
  mul_assoc  := real_mul_assoc
  mul_comm   := real_mul_Commutative
  mul_neut   := real_mul_1_Netural
  mul_inv    := real_mul_inverse_nonzero
  distribLeft := real_mul_add_Distributive.left
  zero_neq_one := real_zero_neq_one

theorem Field_IsDistributive {A : Type} [Field_ A] : IsDistributive A Field_.mul Field_.add := by
  unfold IsDistributive
  unfold IsDistributiveFromLeft
  unfold IsDistributiveFromRight

  apply And.intro
  exact Field_.distribLeft
  intro a b c
  have ThisEQ : Field_.mul (Field_.add b c) a = Field_.mul a (Field_.add b c) := by rw[Field_.mul_comm]
  have ThisE1 : (Field_.mul a b) = (Field_.mul b a) := by rw[Field_.mul_comm]
  have ThisE12 : (Field_.mul a c) = (Field_.mul c a) := by rw[Field_.mul_comm]
  have ThisEQ2 : Field_.add (Field_.mul b a) (Field_.mul c a) =  Field_.add (Field_.mul a b) (Field_.mul a c) :=
  by
    rw[ThisE1]
    rw[ThisE12]


  rw[ThisEQ]
  rw[ThisEQ2]
  exact Field_.distribLeft a b c



 theorem ForEveryElementInFieldExistOnlyOneInvertNumberForAdd
 {A : Type} [Field_ A] (a : A) :
  ∃! b : A, Field_.add a b = Field_.zero := by

    obtain ⟨b,hb⟩   := Field_.add_inv a
    apply ExistsUnique.intro b
    exact hb.left
    intro y h
    have h1 : Field_.add a y = Field_.add a b := by
      rw [hb.left]
      exact h
    have h2 : Field_.add b (Field_.add a y) = Field_.add b (Field_.add a b)  := by
      rw[h]
      rw[hb.left]
    have h3 : Field_.add y (Field_.zero) = Field_.add b (Field_.zero) := by
      conv =>
        rhs
        rw [← hb.left]
      rw[← hb.right]
      rw[← Field_.add_assoc] at h2
      rw[← Field_.add_comm ] at h2
      exact h2
    have neut_y := (Field_.add_neut y).right
    have neut_b := (Field_.add_neut b).right
    rw [neut_y, neut_b] at h3
    exact h3

--אותה הוכחה בדיוק פשוט החלפנו 0 ב1
theorem ForEveryNonZeroElementInFieldExistOnlyOneInvertNumberForMul {A : Type} [Field_ A] (a : A) (ha : a ≠ Field_.zero) :
  ∃! b : A, Field_.mul a b = Field_.one := by
      obtain ⟨b,hb⟩   := Field_.mul_inv a ha
      apply ExistsUnique.intro b
      exact hb.left
      intro y h
      have h1 : Field_.mul a y = Field_.mul a b := by
        rw [hb.left]
        exact h
      have h2 : Field_.mul b (Field_.mul a y) = Field_.mul b (Field_.mul a b)  := by
        rw[h]
        rw[hb.left]
      have h3 : Field_.mul y (Field_.one) = Field_.mul b (Field_.one) := by
        conv =>
          rhs
          rw [← hb.left]
        rw[← hb.right]
        rw[← Field_.mul_assoc] at h2
        rw[← Field_.mul_comm ] at h2
        exact h2
      have neut_y := (Field_.mul_neut y).right
      have neut_b := (Field_.mul_neut b).right
      rw [neut_y, neut_b] at h3
      exact h3

noncomputable def neg {A : Type} [Field_ A] (a : A) : A :=
  Classical.choose (Field_.add_inv a)
prefix:max "-" => neg

theorem neg_inv_cancel_ {A : Type} [Field_ A] (a : A) :
  Field_.add a (neg a) = Field_.zero ∧ Field_.add (neg a) a = Field_.zero:= by
   exact (Classical.choose_spec (Field_.add_inv a))


noncomputable def inv {A : Type} [Field_ A] (a : A) (ha : a ≠ Field_.zero) : A :=
  Classical.choose (Field_.mul_inv a ha)

theorem mul_inv_cancel_ {A : Type} [Field_ A] (a : A) (ha : a ≠ Field_.zero) :
  Field_.mul a (inv a ha) = Field_.one ∧  Field_.mul (inv a ha) a = Field_.one := by
  exact (Classical.choose_spec (Field_.mul_inv a ha))


theorem EveryThingsTimesZeroIsZero {A : Type} [Field_ A] (a : A) : Field_.mul (a) (Field_.zero) = Field_.zero ∧  Field_.mul (Field_.zero) (a) = Field_.zero := by
  have h : Field_.add (Field_.zero : A) Field_.zero = Field_.zero := by
    exact (Field_.add_neut (Field_.zero : A)).left
  have h1 : Field_.mul a (Field_.add (Field_.zero : A) Field_.zero) = Field_.add (Field_.mul a Field_.zero) (Field_.mul a Field_.zero) :=by
    apply Field_IsDistributive.left
  have h2 : Field_.mul a (Field_.add (Field_.zero : A) Field_.zero) = Field_.mul a Field_.zero := by
    rw[h]
  have h3 : Field_.add (Field_.mul a Field_.zero) (Field_.mul a Field_.zero) = Field_.mul a Field_.zero := by
    rw[←h1]
    rw[h2]
  have h4 :  (Field_.mul a Field_.zero)  = Field_.zero := by
    have h4_1 : Field_.add (Field_.add (Field_.mul a Field_.zero) (Field_.mul a Field_.zero)) (neg (Field_.mul a Field_.zero)) = Field_.add (Field_.mul a Field_.zero) (neg (Field_.mul a Field_.zero)) := by
      rw [h3]
    rw [Field_.add_assoc] at h4_1
    rw [(neg_inv_cancel_ (Field_.mul a Field_.zero)).left] at h4_1
    have h_neut : Field_.add (Field_.mul a Field_.zero) Field_.zero = Field_.mul a Field_.zero :=
      (Field_.add_neut (Field_.mul a Field_.zero)).right
    rw [h_neut] at h4_1
    exact h4_1
  apply And.intro
  exact h4
  rw [Field_.mul_comm]
  exact h4




theorem IfMulEQZeroSoaorbEQz {A : Type} [Field_ A] (a : A) (b : A) : Field_.mul a b = Field_.zero → a = Field_.zero ∨ b = Field_.zero := by
  intro h
  have h2 : a ≠ Field_.zero → b = Field_.zero := by
    intro h4
    have h2_1 : Field_.mul (inv a h4) (Field_.mul a b) = b := by
      rw [←Field_.mul_assoc]
      rw[(mul_inv_cancel_ a h4).right]
      exact (Field_.mul_neut b).left
    rw[←h2_1]
    rw[h]
    apply (EveryThingsTimesZeroIsZero (inv a h4)).left
  by_cases ha : a = Field_.zero
  ·
    exact Or.inl ha

  ·
    have hb : b = Field_.zero := h2 ha
    exact Or.inr hb
theorem IfMulEQZeroSoaorbEQzAndIforbEq {A : Type} [Field_ A] (a : A) (b : A) :
  Field_.mul a b = Field_.zero ↔ a = Field_.zero ∨ b = Field_.zero := by

  constructor
  ·
    exact IfMulEQZeroSoaorbEQz a b

  ·
    intro h
    cases h with
    | inl ha =>
      rw [ha]
      rw [Field_.mul_comm Field_.zero b]
      exact (EveryThingsTimesZeroIsZero b).left
    | inr hb =>
      rw [hb]
      exact (EveryThingsTimesZeroIsZero a).left

theorem ZeroHasNoInverse {A : Type} [Field_ A] :
  ∀ a : A, Field_.mul Field_.zero a ≠  Field_.one := by
  intro a
  rw [(EveryThingsTimesZeroIsZero a).right]
  exact Field_.zero_neq_one
