import LinerAlgbra.chapter1_5

/-
============================================================
 פרק 1.6 — מטריצת המקדמים של מערכת לינארית
============================================================
הספר (עמ' 56):
  "מערכת לינארית מעל שדה F מאופיינת לחלוטין על ידי המקדמים שלה.
   אי לכך, במקום לרשום מערכת לינארית במלואה, נוח לרשום בקיצור
   רק את המקדמים שלה."

  "מלבן של סקלרים שיש בו m שורות ו-n עמודות מכונה מטריצה מסדר m×n."

כלומר: קודם המערכת, ואז המטריצה שלה. וכאן גם ניתן שם לטיפוס עצמו.
-/

-- ==========================================
-- 1.6.1  טיפוס המטריצה
-- ==========================================

/-- מטריצה מסדר m×n מעל A: מלבן סקלרים, m שורות ו-n עמודות.
    זו m-יה של n-יות, ולכן כל מה שהוכחנו ב-1.3 על Ntuple
    חל על השורות שלה ללא שינוי. -/
def Matrix_ (A : Type) (m n : Nat) : Type := Ntuple (Ntuple A n) m

/-- מטריצה מורחבת: n עמודות מקדמים, ועוד עמודה אחת (מספר n+1)
    שבה רשומים המקדמים החופשיים. -/
abbrev AugMatrix (A : Type) (m n : Nat) : Type := Matrix_ A m (n + 1)

/-- שתי מטריצות שוות אם כל האיברים שלהן שווים. -/
theorem Matrix_eq {A : Type} {m n : Nat} (M N : Matrix_ A m n)
    (h : ∀ (i : Fin m) (j : Fin n), M i j = N i j) : M = N := by
  funext i j
  exact h i j

-- ==========================================
-- 1.6.2  המטריצות של מערכת לינארית
-- ==========================================

/-- מטריצת המקדמים: השורה ה-i היא המקדמים של המשוואה ה-i. -/
def coefficientMatrix {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) : Matrix_ A m n :=
  fun row => (sys.equations row).a

/-- וקטור המקדמים החופשיים. -/
def freeCoefficientVector {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) : Ntuple A m :=
  fun row => (sys.equations row).b

/-- המטריצה המורחבת: n העמודות הראשונות הן המקדמים,
    והעמודה האחרונה היא האיברים החופשיים. -/
def augmentedMatrix {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) : AugMatrix A m n :=
  fun row column =>
    if h : column.val < n then
      (sys.equations row).a ⟨column.val, h⟩
    else
      (sys.equations row).b
