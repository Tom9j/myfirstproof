import Mathlib.Data.Real.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.RingTheory.Localization.FractionRing



def Operation (A : Type) : Type := A → A → A
-- הפעולה הזאת מיותרת מוסיף אותה כדאי להתרגל לכתיבה של lean
def IsClosedOp (A : Type) (op : Operation A) : Prop := ∀ a b : A, ∃ c : A, c = op a b

def IsCommutativeOp (A : Type) (op : Operation A) : Prop := ∀ a b : A, op a b = op b a

def IsAssociativeOp (A : Type) (op : Operation A) : Prop := ∀ a b c : A, op  (op a b) c = op a (op b c)

def IsDistributiveFromLeft (A:Type) (op1 : Operation A) (op2 : Operation A) : Prop := ∀ a b c : A, op1 a (op2 b c) = op2 (op1 a b) (op1 a c)

def IsDistributiveFromRight (A:Type) (op1 : Operation A) (op2 : Operation A) : Prop := ∀ a b c : A, op1 (op2 b c) a = op2 (op1 b a) (op1 c a)

def IsDistributive (A:Type) (op1 : Operation A) (op2 : Operation A) : Prop := IsDistributiveFromLeft A op1 op2 ∧ IsDistributiveFromRight A op1 op2

-- הגדרה: האם איבר ספציפי e הוא ניטרלי
def IsNeutralElement (A : Type) (op : Operation A) (e : A) : Prop :=
  ∀ a : A, op e a = a ∧ op a e = a

-- הגדרה: האם לקבוצה יש איבר ניטרלי (משתמשת בהגדרה הקודמת)
def HasNeutralMember (A : Type) (op : Operation A) : Prop :=
  ∃ e : A, IsNeutralElement A op e

def IsInverseElement (A : Type) (op : Operation A) (e:A) (he: IsNeutralElement A op e) (a:A) : Prop := ∃ b : A, op a b = e ∧ op b a = e


def AllElementsHaveInverse (A : Type) (op : Operation A) (e:A) (he: IsNeutralElement A op e) : Prop :=
  ∀ a : A, IsInverseElement A op e he a


-- משפט: לטבעיים החיוביים (ℕ+) אין איבר נטרלי תחת פעולת החיבור.
-- הרעיון: אם היה איבר נטרלי e, אז e + e = e.
-- אבל בטבעיים החיוביים, e ≥ 1, ולכן e + e ≥ 2 > e — סתירה!
theorem pnat_add_no_identity : ¬ HasNeutralMember ℕ+ (· + ·) := by
  intro h1
  obtain ⟨e, he⟩ := h1
  -- נקבל מהנחה: e + e = e (על ידי בחירת a = e בתנאי השמאלי)
  have h : e + e = e := (he e).1
  -- נמיר ל-ℕ ונקבל: e + e = e כמספרים טבעיים רגילים
  have hN : (e : ℕ) + (e : ℕ) = (e : ℕ) := by exact_mod_cast h
  -- כל pnat מקיים e ≥ 1
  have hpos : 1 ≤ (e : ℕ) := e.pos
  -- omega פותר: e ≥ 1 ולכן e + e ≥ 2 > e — סתירה
  omega

-- משפט: לכל היותר איבר ניטרלי אחד
theorem ATypeHasAtMostOneNeutralElement (A : Type) (op : Operation A) :
  -- לכל שני איברים שתביא לי:
  ∀ e1 e2 : A,
  -- אם e1 ניטרלי:
  IsNeutralElement A op e1 →
  -- ואם e2 ניטרלי:
  IsNeutralElement A op e2 →
  -- אז הם חייבים להיות שווים:
  e1 = e2 := by
    intro e1 e2 he1 he2
    have h_e1_left : op e1 e2 = e2 := (he1 e2).1
    have h_e2_right : op e1 e2 = e1 := (he2 e1).2
    rw [h_e1_left] at h_e2_right
    have equal : e1 = e2 := by rw [h_e2_right]
    exact equal



theorem IfTypeHasNeutralElementThenItIsUnique (A : Type) (op : Operation A) (h: HasNeutralMember A op) : ∃! e1 : A, ∀a : A, op e1 a = a ∧ op a e1 = a := by
    obtain ⟨e, he⟩ := h
    use e
    apply And.intro
    exact he
    intro e2 he2
    -- הסדר משנה למה? כי התנאי מבקש
    -- ∀ (y : A), (fun e1 => ∀ (a : A), op e1 a = a ∧ op a e1 = a) y → y = e
    -- במילים אחרות אם האיבר נטרלי
    -- אז y = e
    -- ולא e = y
    -- ואז שמפעילים את המשפט הוא מחזיר משפט y = e כי במשפט הy זה הe1
    apply ATypeHasAtMostOneNeutralElement A op e2 e he2 he





-- ============================
-- משפטים על הרציונליים (ℚ)
-- ============================

theorem rat_add_closed : IsClosedOp ℚ (· + ·) := by
  intro a b
  use (a + b)

theorem rat_mul_closed : IsClosedOp ℚ (· * ·) := by
  intro a b
  use (a * b)

theorem rat_mul_assoc : IsAssociativeOp ℚ (· * ·) := by
  intro a b c
  ring

theorem rat_add_assoc : IsAssociativeOp ℚ (· + ·) := by
  intro a b c
  ring

theorem rat_add_Commutative : IsCommutativeOp ℚ (· + ·) := by
  intro a b
  ring

theorem rat_mul_Commutative : IsCommutativeOp ℚ (· * ·) := by
  intro a b
  ring

theorem rat_mul_1_Netural : IsNeutralElement ℚ (· * ·) 1 := by
  intro a
  have left_side : 1 * a = a := by ring
  apply And.intro
  · exact left_side
  · rw [rat_mul_Commutative]
    exact left_side

theorem rat_add_0_Netural : IsNeutralElement ℚ (· + ·) 0 := by
  intro a
  have left_side : 0 + a = a := by ring
  apply And.intro
  · exact left_side
  · rw [rat_add_Commutative]
    exact left_side

theorem rat_mul_add_Distributive : IsDistributive ℚ (· * ·) (· + ·) := by
  apply And.intro
  · intro a b c
    ring
  · intro a b c
    ring

theorem rat_add_inverse : AllElementsHaveInverse ℚ (· + ·) 0 rat_add_0_Netural := by
  intro a
  use -a
  apply And.intro
  · ring
  · ring

theorem rat_mul_inverse_nonzero (a : ℚ) (ha : a ≠ 0) : IsInverseElement ℚ (· * ·) 1 rat_mul_1_Netural a := by
  use a⁻¹
  apply And.intro
  · exact mul_inv_cancel₀ ha
  · exact inv_mul_cancel₀ ha



theorem rat_zero_neq_one : (0 : ℚ) ≠ 1 := by norm_num
theorem real_zero_neq_one : (0 : ℝ) ≠ 1 := by norm_num

-- ============================
-- משפטים על הממשיים (ℝ)
-- ============================

theorem real_add_closed : IsClosedOp ℝ (· + ·) := by
  intro a b
  use (a + b)

theorem real_mul_closed : IsClosedOp ℝ (· * ·) := by
  intro a b
  use (a * b)

theorem real_mul_assoc : IsAssociativeOp ℝ (· * ·) := by
  intro a b c
  ring

theorem real_add_assoc : IsAssociativeOp ℝ (· + ·) := by
  intro a b c
  ring

theorem real_add_Commutative : IsCommutativeOp ℝ (· + ·) := by
  intro a b
  ring

theorem real_mul_Commutative : IsCommutativeOp ℝ (· * ·) := by
  intro a b
  ring

theorem real_mul_1_Netural : IsNeutralElement ℝ (· * ·) 1 := by
  intro a
  have left_side : 1 * a = a := by ring
  apply And.intro
  · exact left_side
  · rw [real_mul_Commutative]
    exact left_side

theorem real_add_0_Netural : IsNeutralElement ℝ (· + ·) 0 := by
  intro a
  have left_side : 0 + a = a := by ring
  apply And.intro
  · exact left_side
  · rw [real_add_Commutative]
    exact left_side

theorem real_mul_add_Distributive : IsDistributive ℝ (· * ·) (· + ·) := by
  apply And.intro
  · intro a b c
    ring
  · intro a b c
    ring

theorem real_add_inverse : AllElementsHaveInverse ℝ (· + ·) 0 real_add_0_Netural := by
  intro a
  use -a
  apply And.intro
  · ring
  · ring

theorem real_mul_inverse_nonzero (a : ℝ) (ha : a ≠ 0) : IsInverseElement ℝ (· * ·) 1 real_mul_1_Netural a := by
  use a⁻¹
  apply And.intro
  · exact mul_inv_cancel₀ ha
  · exact inv_mul_cancel₀ ha
