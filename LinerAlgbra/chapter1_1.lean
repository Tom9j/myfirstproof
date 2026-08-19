import Mathlib.Data.Real.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.RingTheory.Localization.FractionRing



def Operation (A B C : Type) : Type := A → B → C

-- הפעולה הזאת מיותרת מוסיף אותה כדאי להתרגל לכתיבה של lean
def IsClosedOp (A : Type) (op : Operation A A A) : Prop := ∀ a b : A, ∃ c : A, c = op a b

def IsCommutativeOp (A : Type) {C : Type} (op : A → A → C) : Prop := ∀ a b : A, op a b = op b a

def IsAssociativeOp (A : Type) (op : Operation A A A) : Prop := ∀ a b c : A, op  (op a b) c = op a (op b c)

def IsDistributiveFromLeft (A:Type) (op1 : Operation A A A) (op2 : Operation A A A) : Prop := ∀ a b c : A, op1 a (op2 b c) = op2 (op1 a b) (op1 a c)

def IsDistributiveFromRight (A:Type) (op1 : Operation A A A) (op2 : Operation A A A) : Prop := ∀ a b c : A, op1 (op2 b c) a = op2 (op1 b a) (op1 c a)

def IsDistributive (A:Type) (op1 : Operation A A A) (op2 : Operation A A A) : Prop := IsDistributiveFromLeft A op1 op2 ∧ IsDistributiveFromRight A op1 op2

-- הגדרה: האם איבר ספציפי e הוא ניטרלי
def IsNeutralElement (A : Type) (op : Operation A A A) (e : A) : Prop :=
  ∀ a : A, op e a = a ∧ op a e = a

-- הגדרה: האם לקבוצה יש איבר ניטרלי (משתמשת בהגדרה הקודמת)
def HasNeutralMember (A : Type) (op : Operation A A A) : Prop :=
  ∃ e : A, IsNeutralElement A op e

def IsInverseElement (A : Type) (op : Operation A A A) (e:A) (he: IsNeutralElement A op e) (a:A) : Prop := ∃ b : A, op a b = e ∧ op b a = e


def AllElementsHaveInverse (A : Type) (op : Operation A A A) (e:A) (he: IsNeutralElement A op e) : Prop :=
  ∀ a : A, IsInverseElement A op e he a


-- משפט: לטבעיים החיוביים (ℕ+) אין איבר נטרלי תחת פעולת החיבור.
-- הרעיון: אם היה איבר נטרלי e, אז e + e = e.
-- אבל בטבעיים החיוביים, e ≥ 1, ולכן e + e ≥ 2 > e — סתירה!
theorem PNatNoAdditiveIdentity : ¬ HasNeutralMember ℕ+ (· + ·) := by
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
theorem NeutralElementIsUnique (A : Type) (op : Operation A A A) :
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



theorem ExistsUniqueNeutralElement (A : Type) (op : Operation A A A) (h: HasNeutralMember A op) : ∃! e1 : A, ∀a : A, op e1 a = a ∧ op a e1 = a := by
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
    apply NeutralElementIsUnique A op e2 e he2 he
