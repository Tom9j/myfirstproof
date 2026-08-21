import LinerAlgbra.chapter1_9

/-
============================================================
 פרק 1.10 — מטריצות מדרגות
============================================================
הספר (עמ' 79):
  "בכל שלוש הדוגמאות מסעיף 1.9 השיטה הייתה דומה... מטרתנו היא
   להראות שהשיטה הזאת 'פועלת' תמיד. כצעד ראשון - נאפיין את
   טיפוס המערכת שאליה אנו רוצים להגיע."

כלומר: 1.9 הראה שהשיטה עובדת בדוגמאות; 1.10 מגדיר לאן היא
אמורה להגיע, ו-1.10.5 יוכיח שתמיד אפשר להגיע לשם.
-/

-- ============================================================
-- הגדרה 1.10.1 — שורת אפס, איבר פותח  (הספר, עמ' 79)
-- ============================================================

/-- א. שורת אפס: שורה שכל איבריה אפסים.

    הערת שוליים 1 בספר: שורת אפס במטריצת המקדמים של מערכת
    לינארית מייצגת משוואת אפס במערכת עצמה. -/
def IsZeroRow {A : Type} [Field_ A] {n : Nat} (row : Ntuple A n) : Prop :=
  ∀ j : Fin n, row j = Field_.zero

/-- ב. j הוא האינדקס של האיבר הפותח של השורה: הערך בעמודה j
       שונה מאפס, וכל העמודות שמשמאלו הן אפס.

    "האיבר הראשון משמאל ששונה מ-0" מתורגם כאן ל:
      "שונה מ-0"  ∧  "כל מה שמשמאלו הוא 0"

    שים לב שזה **פרדיקט ולא פונקציה**. פונקציה שמחזירה את האינדקס
    הייתה חייבת להכריע לכל j האם row j = zero, ובשדה כללי אין לנו
    DecidableEq. הניסוח הזה לא דורש שום הכרעה ועובד מעל כל שדה.

    הערת שוליים 2 בספר: במטריצת המקדמים של מערכת, האיבר הפותח של
    שורה הוא המקדם של המשתנה הראשון שמופיע במשוואה המתאימה. -/
def IsLeadingIndex {A : Type} [Field_ A] {n : Nat}
    (row : Ntuple A n) (j : Fin n) : Prop :=
  row j ≠ Field_.zero ∧ ∀ k : Fin n, k < j → row k = Field_.zero

-- ------------------------------------------------------------
-- שלושה משפטים שמצדיקים את ההגדרה
-- ------------------------------------------------------------

/-- לשורת אפס אין איבר פותח. -/
theorem not_IsLeadingIndex_of_IsZeroRow {A : Type} [Field_ A] {n : Nat}
    (row : Ntuple A n) (hzero : IsZeroRow row) (j : Fin n) :
    ¬ IsLeadingIndex row j := by
  intro hlead
  exact hlead.left (hzero j)

/-- שורה שיש לה איבר פותח אינה שורת אפס. -/
theorem not_IsZeroRow_of_IsLeadingIndex {A : Type} [Field_ A] {n : Nat}
    (row : Ntuple A n) (j : Fin n) (hlead : IsLeadingIndex row j) :
    ¬ IsZeroRow row := by
  intro hzero
  exact hlead.left (hzero j)

/-- יחידות: לשורה יש לכל היותר איבר פותח אחד.
    זו ההצדקה למילה "ה" ב"**ה**איבר הפותח".

    התרגיל שלך. הרעיון: לפי טריכוטומיה, או j₁ < j₂ או j₁ = j₂
    או j₂ < j₁. במקרה הראשון, h₂.right נותן ש-row j₁ = zero,
    בסתירה ל-h₁.left. המקרה השלישי סימטרי.
    שימושי:  lt_trichotomy j₁ j₂   -- מפצל לשלושת המקרים -/
theorem IsLeadingIndex_unique {A : Type} [Field_ A] {n : Nat}
    (row : Ntuple A n) (j₁ j₂ : Fin n)
    (h₁ : IsLeadingIndex row j₁) (h₂ : IsLeadingIndex row j₂) :
    j₁ = j₂ := by
  sorry

/-- קיום: לשורה שאינה שורת אפס יש איבר פותח.

    כאן נכנסת הלוגיקה הקלאסית, ולכן השארתי את זה לנו יחד:
    מ-¬(∀ j, row j = zero) צריך להגיע ל-∃ j, row j ≠ zero
    (שלילה כפולה), ואז לבחור את ה-j המינימלי מביניהם.
    התוצאה לא תחשב - בדיוק כמו neg ו-inv שלך. -/
theorem exists_IsLeadingIndex {A : Type} [Field_ A] {n : Nat}
    (row : Ntuple A n) (hnot : ¬ IsZeroRow row) :
    ∃ j : Fin n, IsLeadingIndex row j := by
  sorry

-- ------------------------------------------------------------
-- האיבר הפותח כפונקציה
--
-- הפרדיקט למעלה אומר "מה זה אומר להיות האיבר הפותח". כאן אנחנו
-- בונים אותו בפועל: מקלפים את השורה משמאל כל עוד רואים אפס, וברגע
-- שנתקלים במשהו שאינו אפס - עוצרים.
--
-- ההנחה  row ≠ Ntuple_zero  עובדת פעמיים:
--   1. היא פוסלת את המקרה n = 0 (שורה באורך אפס היא בהכרח אפס)
--   2. היא מייצרת את ההנחה לקריאה הרקורסיבית
--
-- למה noncomputable: כדי להסתעף צריך להכריע האם row 0 = zero,
-- ובשדה כללי אין DecidableEq. open Classical נותן את ההכרעה
-- כאקסיומה, ולכן הפונקציה קיימת אבל לא רצה.
-- זה אותו מצב בדיוק כמו neg ו-inv שלך ב-chapter1_2.
-- (אם תוסיף [DecidableEq A] בחתימה - זה יהפוך לחישובי, ומעל ℚ
--  אפשר יהיה להריץ עליו #eval.)
-- ------------------------------------------------------------

/-- זנב של n-יה: זורקים את האיבר הראשון משמאל. -/
def Ntuple_tail {A : Type} {n : Nat} (row : Ntuple A (n + 1)) : Ntuple A n :=
  fun j => row (Fin.succ j)

/-- הניסוח הנקודתי והניסוח הגלובלי של "שורת אפס" שקולים. -/
theorem IsZeroRow_iff_eq_zero {A : Type} [Field_ A] {n : Nat}
    (row : Ntuple A n) : IsZeroRow row ↔ row = Ntuple_zero := by
  constructor
  · intro h
    funext j
    exact h j
  · intro h
    intro j
    rw [h]
    rfl

open Classical in
/-- האינדקס של האיבר הפותח, כפונקציה. -/
noncomputable def leadingIndex {A : Type} [Field_ A] :
    {n : Nat} → (row : Ntuple A n) → row ≠ Ntuple_zero → Fin n
  | 0, row, he =>
      -- שורה באורך אפס שווה ל-Ntuple_zero, אז ההנחה he סותרת
      absurd (by funext j; exact Fin.elim0 j) he
  | _ + 1, row, he =>
      if h : row 0 = Field_.zero then
        -- האיבר הראשון אפס: מקלפים וממשיכים, ומזיזים את האינדקס אחד ימינה
        Fin.succ (leadingIndex (Ntuple_tail row) (by
          intro htail
          apply he
          funext j
          refine Fin.cases ?_ ?_ j
          · exact h
          · intro i
            exact congrFun htail i))
      else
        -- האיבר הראשון שונה מאפס: זה הוא
        0

/-- מה שהפונקציה מחזירה הוא באמת האיבר הפותח.

    זה המשפט שהופך את הפונקציה לשימושית: בלעדיו `leadingIndex`
    מחזירה איזשהו Fin n, ושום דבר בטיפוס לא מבטיח שהוא הנכון.
    הפרדיקט הוא המפרט, הפונקציה היא המימוש.

    נעשה יחד - זו אינדוקציה על n שצריכה לפרק את ה-dite. -/
theorem leadingIndex_spec {A : Type} [Field_ A] :
    ∀ {n : Nat} (row : Ntuple A n) (he : row ≠ Ntuple_zero),
      IsLeadingIndex row (leadingIndex row he) := by
  sorry

-- הערה: יש דרך קצרה יותר לאותה מטרה, בדיוק בתבנית של neg ו-inv שלך:
--
--   noncomputable def leadingIndex' (row) (he) : Fin n :=
--     Classical.choose (exists_IsLeadingIndex row he)
--   theorem leadingIndex'_spec (row) (he) :
--       IsLeadingIndex row (leadingIndex' row he) :=
--     Classical.choose_spec (exists_IsLeadingIndex row he)
--
-- שם המפרט יוצא בחינם, אבל כל העבודה עוברת ל-exists_IsLeadingIndex.
-- הגרסה הרקורסיבית למעלה מראה את האלגוריתם במפורש, וזה שווה יותר
-- ללמידה.

-- ------------------------------------------------------------
-- בדיקה קונקרטית של ההגדרה, על הדוגמה של הספר (עמ' 79)
--
--   ⎡ 0 0 0 8 7 ⎤   ← איבר פותח בעמודה 3 (הספר: a₁₄ = 8)
--   ⎢ 7 2 3 4 3 ⎥   ← איבר פותח בעמודה 0 (הספר: a₂₁ = 7)
--   ⎢ 0 0 0 0 0 ⎥   ← שורת אפס, אין איבר פותח
--   ⎢ 0 9 0 5 1 ⎥   ← איבר פותח בעמודה 1 (הספר: a₄₂ = 9)
--   ⎣ 0 6 2 1 4 ⎦   ← איבר פותח בעמודה 1 (הספר: a₅₂ = 6)
--
-- הספר ממספר עמודות מ-1, אנחנו מ-0, ולכן a₁₄ יושב אצלנו בעמודה 3.
-- ------------------------------------------------------------

def bookRow1 : Ntuple ℚ 5 := fun j =>
  match j with
  | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 8 | 4 => 7

def bookRow2 : Ntuple ℚ 5 := fun j =>
  match j with
  | 0 => 7 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 3

def bookRow3 : Ntuple ℚ 5 := fun j =>
  match j with
  | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 0 | 4 => 0

-- הבדיקה החיובית: ההגדרה מזהה את האיבר הפותח הנכון
example : IsLeadingIndex bookRow1 3 := by
  unfold IsLeadingIndex
  decide

example : IsLeadingIndex bookRow2 0 := by
  unfold IsLeadingIndex
  decide

-- הבדיקה השלילית, והיא החשובה: עמודה 4 מכילה 7 ≠ 0,
-- ובכל זאת היא **לא** האיבר הפותח — כי משמאלה יש 8 שאינו אפס.
-- אילו שכחנו את התנאי השני בהגדרה, הבדיקה הזאת הייתה נכשלת.
example : ¬ IsLeadingIndex bookRow1 4 := by
  unfold IsLeadingIndex
  decide

-- שורת אפס
example : IsZeroRow bookRow3 := by
  unfold IsZeroRow
  decide

example (j : Fin 5) : ¬ IsLeadingIndex bookRow3 j :=
  not_IsLeadingIndex_of_IsZeroRow bookRow3 (by unfold IsZeroRow; decide) j

-- ============================================================
-- הגדרה 1.10.2 — מטריצת מדרגות  (הספר, עמ' 80)
-- ============================================================

/-- מטריצת מדרגות.

    א. בכל שורה שאינה שורת אפס, האיבר הפותח הוא מימין לאיברים
       הפותחים של השורות שמעליה.

       "מימין" = אינדקס עמודה **גדול** יותר. הטקסט בספר נקרא
       מימין לשמאל, אבל המטריצות נכתבות משמאל לימין ואנחנו
       ממספרים עמודות 0,1,2,... משמאל.

    ב. כל שורות האפס הן מתחת לכל השורות שאינן שורות אפס.

       נוסח כאן בצורה השקולה "מתחת לשורת אפס יש רק שורות אפס",
       שנוחה יותר: מתחילים משורת אפס ומסיקים על מה שמתחתיה.

    שים לב שצריך את שני התנאים: תנאי א מדבר רק על שורות שאינן
    אפס, ולכן הוא לבדו מרשה שורת אפס באמצע המטריצה. -/
def IsEchelon {A : Type} [Field_ A] {m n : Nat} (M : Matrix_ A m n) : Prop :=
  (∀ (i₁ i₂ : Fin m) (j₁ j₂ : Fin n),
      i₁ < i₂ →
      IsLeadingIndex (M i₁) j₁ →
      IsLeadingIndex (M i₂) j₂ →
      j₁ < j₂)
  ∧
  (∀ (i₁ i₂ : Fin m), i₁ < i₂ → IsZeroRow (M i₁) → IsZeroRow (M i₂))

/-- ג (חלק ג של הגדרה 1.10.1, שמפנה קדימה לכאן):
    j היא עמודה שבה יושב איבר פותח של המטריצה. -/
def IsPivotColumn {A : Type} [Field_ A] {m n : Nat}
    (M : Matrix_ A m n) (j : Fin n) : Prop :=
  ∃ i : Fin m, IsLeadingIndex (M i) j

-- ------------------------------------------------------------
-- בדיקה שההגדרה עושה את מה שהתכוונו
-- ------------------------------------------------------------

/-- מטריצת האפס היא מטריצת מדרגות.
    הספר מציין את זה במפורש: "היא עונה על הדרישות למטריצת מדרגות,
    כי אין בה שורות שאינן שורות אפס."
    שני התנאים מתקיימים ריקנית. -/
theorem IsEchelon_zeroMatrix {A : Type} [Field_ A] {m n : Nat} :
    IsEchelon (fun (_ : Fin m) (_ : Fin n) => (Field_.zero : A)) := by
  constructor
  -- תנאי א: אין בכלל שורה עם איבר פותח, אז אין מה לבדוק
  · intro i₁ i₂ j₁ j₂ horder hlead₁ hlead₂
    exact absurd rfl (And.left hlead₁)
  -- תנאי ב: כל שורה היא שורת אפס
  · intro i₁ i₂ horder hzero j
    rfl

-- ============================================================
-- הגדרה 1.10.3 — מערכת לינארית מדורגת  (הספר, עמ' 81)
-- ============================================================

/-- "מערכת לינארית, אשר **מטריצת המקדמים** שלה היא מטריצת מדרגות,
    נקראת מערכת (לינארית) מדורגת."

    שים לב: מטריצת ה**מקדמים** (n עמודות), לא המורחבת (n+1). -/
def IsEchelonSystem {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) : Prop :=
  IsEchelon (coefficientMatrix sys)

/-- "'לדרג מערכת לינארית' משמעו לעבור ממנה למערכת מדורגת, באמצעות
    מספר סופי של שינויים אלמנטריים עוקבים." -/
def CanBeEchelonized {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) : Prop :=
  ∃ (length : Nat) (operations : Ntuple (ElementaryOperation A m n) length),
    IsEchelonSystem (applySequence length operations sys)

-- ============================================================
-- הגדרה 1.10.4 — משתנים קשורים וחופשיים  (הספר, עמ' 82)
-- ============================================================

/-- "משתנה של מערכת מדורגת נקרא **משתנה קשור**, אם המקדם המופיע
    לצדו הוא איבר פותח."

    המשתנה ה-j הוא קשור כאשר עמודה j של מטריצת המקדמים מכילה
    איבר פותח של אחת השורות. -/
def IsBoundVariable {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) (j : Fin n) : Prop :=
  IsPivotColumn (coefficientMatrix sys) j

/-- "משתנה של המערכת שאינו קשור נקרא **משתנה חופשי**." -/
def IsFreeVariable {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) (j : Fin n) : Prop :=
  ¬ IsBoundVariable sys j

/-- משתנה קשור אינו חופשי ולהפך - זו ההגדרה, לא משפט. -/
theorem not_IsFreeVariable_iff {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) (j : Fin n) :
    ¬ IsFreeVariable sys j ↔ ¬ ¬ IsBoundVariable sys j := Iff.rfl

/-- כל משתנה הוא קשור או חופשי. הטענה עצמה קלאסית (חוק השלישי
    הנמנע), ולא בנייתית - אי אפשר להכריע לאיזו קטגוריה משתנה שייך
    בלי להכריע שוויון לאפס בשדה. -/
theorem IsBoundVariable_or_IsFreeVariable {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) (j : Fin n) :
    IsBoundVariable sys j ∨ IsFreeVariable sys j :=
  Classical.em (IsBoundVariable sys j)

/-- למשתנה קשור יש שורה שהאיבר הפותח שלה יושב בעמודה שלו.
    זו רק פריקה של ההגדרה, אבל היא מה שמשתמשים בו בפועל. -/
theorem exists_row_of_IsBoundVariable {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) (j : Fin n) (h : IsBoundVariable sys j) :
    ∃ i : Fin m, IsLeadingIndex (coefficientMatrix sys i) j := h

-- ============================================================
-- משפט 1.10.5 — משפט הדירוג  (הספר, עמ' 83)
-- ============================================================

-- ------------------------------------------------------------
-- קודם: שקילות-שורה **בתוך הבלוק בלבד**
--
-- זה התיקון החיוני. "שקילות-שורה + מה שמעל הקו לא זז" אינו מספיק:
-- הפעולה  R7 → R7 + c·R0  (עם k=3) לא מזיזה שורה מעל הקו, ובכל זאת
-- מכניסה לשורה 7 ערכים מהעמודות השמאליות של שורה 0 - והורסת את
-- כל הטיעון. צריך לדרוש שהפעולות **מערבות רק שורות מ-k ומטה**,
-- וזה בדיוק מה שקורה ב-C#: שני האינדקסים בלולאות הם ≥ startRow.
-- ------------------------------------------------------------

/-- הפעולה נוגעת רק בשורות מ-k ומטה. -/
def OpFrom {A : Type} [Field_ A] {m n : Nat} (k : Nat) :
    ElementaryOperation A m n → Prop
  | ElementaryOperation.switchRows i j => k ≤ i.val ∧ k ≤ j.val
  | ElementaryOperation.scaleRow i _ _ => k ≤ i.val
  | ElementaryOperation.addRow i j _ _ => k ≤ i.val ∧ k ≤ j.val

/-- שקילות-שורה שמשתמשת רק בשורות מ-k ומטה. -/
inductive RowEquivalentFrom {A : Type} [Field_ A] {m n : Nat}
    (k : Nat) (M : AugMatrix A m n) : AugMatrix A m n → Prop
  | refl : RowEquivalentFrom k M M
  | step {P : AugMatrix A m n} (op : ElementaryOperation A m n)
      (hop : OpFrom k op) (h : RowEquivalentFrom k M P) :
      RowEquivalentFrom k M (applyMatrixElementaryOperation op P)

/-- שוכחים את ההגבלה. -/
theorem RowEquivalent_of_RowEquivalentFrom {A : Type} [Field_ A] {m n : Nat}
    {k : Nat} {M N : AugMatrix A m n} (h : RowEquivalentFrom k M N) :
    RowEquivalent M N := by
  induction h with
  | refl => exact RowEquivalent.refl
  | step op _ _ ih => exact RowEquivalent.step op ih

-- ------------------------------------------------------------
-- כלי עזר: תרגום בין שורה של מטריצה מורחבת לבין משוואה
--
-- כל הפעולות האלמנטריות על מטריצה עוברות דרך
-- systemFromAugmentedMatrix ואז חזרה דרך augmentedMatrix.
-- במקום להיאבק בכל פעם באינדקסים של Fin, נותנים שם לשני
-- הכיוונים האלה ומוכיחים עליהם שלוש למות. אחרי זה כל
-- ההוכחות למטה הופכות לחישוב קצר.
-- ------------------------------------------------------------

/-- שורה של מטריצה מורחבת, נקראת כמשוואה. -/
def rowToEquation {A : Type} [Field_ A] {n : Nat}
    (row : Ntuple A (n + 1)) : LinearEquation A n :=
  { a := fun j => row ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self n)⟩,
    b := row ⟨n, Nat.lt_succ_self n⟩ }

/-- משוואה, נכתבת כשורה של מטריצה מורחבת. -/
def equationToRow {A : Type} [Field_ A] {n : Nat}
    (equation : LinearEquation A n) : Ntuple A (n + 1) :=
  fun j => if h : j.val < n then equation.a ⟨j.val, h⟩ else equation.b

/-- הגשר: השורה ה-i של augmentedMatrix היא בדיוק המשוואה ה-i. -/
theorem augmentedMatrix_row {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) (i : Fin m) :
    augmentedMatrix sys i = equationToRow (sys.equations i) := rfl

/-- והגשר בכיוון השני. -/
theorem systemFromAugmentedMatrix_row {A : Type} [Field_ A] {m n : Nat}
    (P : AugMatrix A m n) (i : Fin m) :
    (systemFromAugmentedMatrix P).equations i = rowToEquation (P i) := rfl

/-- הלוך ושוב מחזיר את אותה שורה. -/
theorem equationToRow_rowToEquation {A : Type} [Field_ A] {n : Nat}
    (row : Ntuple A (n + 1)) (j : Fin (n + 1)) :
    equationToRow (rowToEquation row) j = row j := by
  unfold equationToRow
  by_cases hj : j.val < n
  · rw [dif_pos hj]
    show row ⟨j.val, Nat.lt_trans hj (Nat.lt_succ_self n)⟩ = row j
    have hidx : (⟨j.val, Nat.lt_trans hj (Nat.lt_succ_self n)⟩ : Fin (n + 1)) = j :=
      Fin.ext rfl
    rw [hidx]
  · rw [dif_neg hj]
    show row ⟨n, Nat.lt_succ_self n⟩ = row j
    have hbound : j.val < n + 1 := j.isLt
    have hval : j.val = n := by omega
    have hidx : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = j := Fin.ext (Eq.symm hval)
    rw [hidx]

/-- כפל משוואה בסקלר = כפל השורה בסקלר, איבר-איבר. -/
theorem equationToRow_smul {A : Type} [Field_ A] {n : Nat}
    (c : A) (equation : LinearEquation A n) (j : Fin (n + 1)) :
    equationToRow
        { a := Ntuple_smul c equation.a, b := Field_.mul c equation.b } j
      = Field_.mul c (equationToRow equation j) := by
  unfold equationToRow
  by_cases hj : j.val < n
  · rw [dif_pos hj]
    rw [dif_pos hj]
    rfl
  · rw [dif_neg hj]
    rw [dif_neg hj]

/-- חיבור משוואה עם כפולה של משוואה = אותו דבר על השורות. -/
theorem equationToRow_addSmul {A : Type} [Field_ A] {n : Nat}
    (c : A) (first second : LinearEquation A n) (j : Fin (n + 1)) :
    equationToRow
        { a := Ntuple_add first.a (Ntuple_smul c second.a),
          b := Field_.add first.b (Field_.mul c second.b) } j
      = Field_.add (equationToRow first j) (Field_.mul c (equationToRow second j)) := by
  unfold equationToRow
  by_cases hj : j.val < n
  · rw [dif_pos hj]
    rw [dif_pos hj]
    rw [dif_pos hj]
    rfl
  · rw [dif_neg hj]
    rw [dif_neg hj]
    rw [dif_neg hj]

-- ------------------------------------------------------------
-- שלוש נוסחאות: מה בדיוק עושה כל פעולה אלמנטרית לאיבר (i,j)
-- ------------------------------------------------------------

theorem applyMatrixOp_entry {A : Type} [Field_ A] {m n : Nat}
    (op : ElementaryOperation A m n) (P : AugMatrix A m n)
    (i : Fin m) (j : Fin (n + 1)) :
    applyMatrixElementaryOperation op P i j
      = equationToRow
          ((applyElementaryOperation op (systemFromAugmentedMatrix P)).equations i) j := rfl

theorem applyMatrixOp_switchRows_entry {A : Type} [Field_ A] {m n : Nat}
    (P : AugMatrix A m n) (r1 r2 i : Fin m) (j : Fin (n + 1)) :
    applyMatrixElementaryOperation (ElementaryOperation.switchRows r1 r2) P i j
      = P (if i = r1 then r2 else if i = r2 then r1 else i) j := by
  rw [applyMatrixOp_entry]
  have hstep :
      (applyElementaryOperation (ElementaryOperation.switchRows r1 r2)
          (systemFromAugmentedMatrix P)).equations i
        = if i = r1 then (systemFromAugmentedMatrix P).equations r2
          else if i = r2 then (systemFromAugmentedMatrix P).equations r1
          else (systemFromAugmentedMatrix P).equations i := rfl
  rw [hstep]
  by_cases h1 : i = r1
  · rw [if_pos h1]
    rw [if_pos h1]
    rw [systemFromAugmentedMatrix_row]
    rw [equationToRow_rowToEquation]
  · rw [if_neg h1]
    rw [if_neg h1]
    by_cases h2 : i = r2
    · rw [if_pos h2]
      rw [if_pos h2]
      rw [systemFromAugmentedMatrix_row]
      rw [equationToRow_rowToEquation]
    · rw [if_neg h2]
      rw [if_neg h2]
      rw [systemFromAugmentedMatrix_row]
      rw [equationToRow_rowToEquation]

theorem applyMatrixOp_scaleRow_entry {A : Type} [Field_ A] {m n : Nat}
    (P : AugMatrix A m n) (r : Fin m) (c : A) (hc : c ≠ Field_.zero)
    (i : Fin m) (j : Fin (n + 1)) :
    applyMatrixElementaryOperation (ElementaryOperation.scaleRow r c hc) P i j
      = if i = r then Field_.mul c (P r j) else P i j := by
  rw [applyMatrixOp_entry]
  have hstep :
      (applyElementaryOperation (ElementaryOperation.scaleRow r c hc)
          (systemFromAugmentedMatrix P)).equations i
        = if i = r then
            { a := Ntuple_smul c ((systemFromAugmentedMatrix P).equations r).a,
              b := Field_.mul c ((systemFromAugmentedMatrix P).equations r).b }
          else (systemFromAugmentedMatrix P).equations i := rfl
  rw [hstep]
  by_cases hir : i = r
  · rw [if_pos hir]
    rw [if_pos hir]
    rw [equationToRow_smul]
    rw [systemFromAugmentedMatrix_row]
    rw [equationToRow_rowToEquation]
  · rw [if_neg hir]
    rw [if_neg hir]
    rw [systemFromAugmentedMatrix_row]
    rw [equationToRow_rowToEquation]

theorem applyMatrixOp_addRow_entry {A : Type} [Field_ A] {m n : Nat}
    (P : AugMatrix A m n) (r s : Fin m) (c : A) (hrs : r ≠ s)
    (i : Fin m) (j : Fin (n + 1)) :
    applyMatrixElementaryOperation (ElementaryOperation.addRow r s c hrs) P i j
      = if i = r then Field_.add (P r j) (Field_.mul c (P s j)) else P i j := by
  rw [applyMatrixOp_entry]
  have hstep :
      (applyElementaryOperation (ElementaryOperation.addRow r s c hrs)
          (systemFromAugmentedMatrix P)).equations i
        = if i = r then
            { a := Ntuple_add ((systemFromAugmentedMatrix P).equations r).a
                     (Ntuple_smul c ((systemFromAugmentedMatrix P).equations s).a),
              b := Field_.add ((systemFromAugmentedMatrix P).equations r).b
                     (Field_.mul c ((systemFromAugmentedMatrix P).equations s).b) }
          else (systemFromAugmentedMatrix P).equations i := rfl
  rw [hstep]
  by_cases hir : i = r
  · rw [if_pos hir]
    rw [if_pos hir]
    rw [equationToRow_addSmul]
    rw [systemFromAugmentedMatrix_row]
    rw [systemFromAugmentedMatrix_row]
    rw [equationToRow_rowToEquation]
    rw [equationToRow_rowToEquation]
  · rw [if_neg hir]
    rw [if_neg hir]
    rw [systemFromAugmentedMatrix_row]
    rw [equationToRow_rowToEquation]

-- שתי הלמות על **פעולה בודדת** בתוך הבלוק. אלה העלים - כל השאר
-- נגזר מהן באינדוקציה.

/-- פעולה בתוך הבלוק לא נוגעת בשורה שמעל הקו. -/
theorem applyOp_fixed_above {A : Type} [Field_ A] {m n : Nat}
    {k : Nat} (op : ElementaryOperation A m n) (hop : OpFrom k op)
    (P : AugMatrix A m n) (i : Fin m) (hi : i.val < k) :
    applyMatrixElementaryOperation op P i = P i := by
  funext j
  cases op with
  | switchRows r1 r2 =>
      have hop2 : k ≤ r1.val ∧ k ≤ r2.val := hop
      obtain ⟨h1, h2⟩ := hop2
      have hne1 : i ≠ r1 := by
        intro heq
        rw [heq] at hi
        omega
      have hne2 : i ≠ r2 := by
        intro heq
        rw [heq] at hi
        omega
      rw [applyMatrixOp_switchRows_entry]
      rw [if_neg hne1]
      rw [if_neg hne2]
  | scaleRow r cc hcc =>
      have hop2 : k ≤ r.val := hop
      have hne : i ≠ r := by
        intro heq
        rw [heq] at hi
        omega
      rw [applyMatrixOp_scaleRow_entry]
      rw [if_neg hne]
  | addRow r s cc hrs =>
      have hop2 : k ≤ r.val ∧ k ≤ s.val := hop
      obtain ⟨h1, h2⟩ := hop2
      have hne : i ≠ r := by
        intro heq
        rw [heq] at hi
        omega
      rw [applyMatrixOp_addRow_entry]
      rw [if_neg hne]

/-- פעולה בתוך הבלוק משמרת "כל השורות בבלוק אפס בעמודות ≤ c".
    הסיבה: צירוף לינארי של אפסים הוא אפס. -/
theorem applyOp_preserves_zeroPrefix {A : Type} [Field_ A] {m n : Nat}
    {k : Nat} (op : ElementaryOperation A m n) (hop : OpFrom k op)
    (P : AugMatrix A m n) (c : Fin (n + 1))
    (hz : ∀ i : Fin m, k ≤ i.val → ∀ j' : Fin (n + 1), j' ≤ c →
            P i j' = Field_.zero) :
    ∀ i : Fin m, k ≤ i.val → ∀ j' : Fin (n + 1), j' ≤ c →
      applyMatrixElementaryOperation op P i j' = Field_.zero := by
  intro i hi j' hj'
  cases op with
  | switchRows r1 r2 =>
      have hop2 : k ≤ r1.val ∧ k ≤ r2.val := hop
      obtain ⟨h1, h2⟩ := hop2
      rw [applyMatrixOp_switchRows_entry]
      by_cases hone : i = r1
      · rw [if_pos hone]
        exact hz r2 h2 j' hj'
      · rw [if_neg hone]
        by_cases htwo : i = r2
        · rw [if_pos htwo]
          exact hz r1 h1 j' hj'
        · rw [if_neg htwo]
          exact hz i hi j' hj'
  | scaleRow r cc hcc =>
      have hop2 : k ≤ r.val := hop
      rw [applyMatrixOp_scaleRow_entry]
      by_cases hir : i = r
      · rw [if_pos hir]
        rw [hz r hop2 j' hj']
        exact And.left (MulByZeroIsZero cc)
      · rw [if_neg hir]
        exact hz i hi j' hj'
  | addRow r s cc hrs =>
      have hop2 : k ≤ r.val ∧ k ≤ s.val := hop
      obtain ⟨h1, h2⟩ := hop2
      rw [applyMatrixOp_addRow_entry]
      by_cases hir : i = r
      · rw [if_pos hir]
        rw [hz r h1 j' hj']
        rw [hz s h2 j' hj']
        rw [And.left (MulByZeroIsZero cc)]
        exact And.left (Field_.add_neut Field_.zero)
      · rw [if_neg hir]
        exact hz i hi j' hj'

-- ואותן שתי תכונות, לסדרה שלמה - באינדוקציה:

theorem RowEquivalentFrom_fixed_above {A : Type} [Field_ A] {m n : Nat}
    {k : Nat} {M N : AugMatrix A m n} (h : RowEquivalentFrom k M N)
    (i : Fin m) (hi : i.val < k) : N i = M i := by
  induction h with
  | refl => rfl
  | step op hop _ ih =>
      rw [applyOp_fixed_above op hop _ i hi]
      exact ih

theorem RowEquivalentFrom_zeroPrefix {A : Type} [Field_ A] {m n : Nat}
    {k : Nat} {M N : AugMatrix A m n} (h : RowEquivalentFrom k M N)
    (c : Fin (n + 1))
    (hz : ∀ i : Fin m, k ≤ i.val → ∀ j' : Fin (n + 1), j' ≤ c →
            M i j' = Field_.zero) :
    ∀ i : Fin m, k ≤ i.val → ∀ j' : Fin (n + 1), j' ≤ c →
      N i j' = Field_.zero := by
  induction h with
  | refl => exact hz
  | step op hop _ ih =>
      exact applyOp_preserves_zeroPrefix op hop _ c ih

-- ------------------------------------------------------------
-- היחס
-- ------------------------------------------------------------

/-- "אפשר לדרג את M ל-N, כשמתחילים משורה k."
    כל בנייה של הוכחה כאן היא ריצה אחת של האלגוריתם. -/
inductive Echelonizes {A : Type} [Field_ A] {m n : Nat} :
    Nat → AugMatrix A m n → AugMatrix A m n → Prop
  | done {k : Nat} {M : AugMatrix A m n}
      (h : ∀ i : Fin m, k ≤ i.val → IsZeroRow (M i)) :
      Echelonizes k M M
  | round {k : Nat} {M Mp N : AugMatrix A m n} {j : Fin (n + 1)}
      (hk      : k < m)
      (hequiv  : RowEquivalentFrom k M Mp)
      (hpivot  : Mp ⟨k, hk⟩ j ≠ Field_.zero)
      (hleft   : ∀ i : Fin m, k ≤ i.val →
                   ∀ j' : Fin (n + 1), j' < j → Mp i j' = Field_.zero)
      (hbelow  : ∀ i : Fin m, k < i.val → Mp i j = Field_.zero)
      (hrest   : Echelonizes (k + 1) Mp N) :
      Echelonizes k M N

-- ------------------------------------------------------------
-- טענה 1: שקילות-שורה. קלה, כמו שאמרת.
-- ------------------------------------------------------------

theorem Echelonizes_RowEquivalent {A : Type} [Field_ A] {m n : Nat}
    {k : Nat} {M N : AugMatrix A m n} (h : Echelonizes k M N) :
    RowEquivalent M N := by
  induction h with
  | done _ =>
      exact RowEquivalent.refl
  | round _ hequiv _ _ _ _ ih =>
      exact RowEquivalent_trans _ _ _
        (RowEquivalent_of_RowEquivalentFrom hequiv) ih

-- ------------------------------------------------------------
-- טענה 2: התוצאה מדורגת. ארבעה סעיפים, אינדוקציה אחת.
-- ------------------------------------------------------------

/-- ארבעת הדברים שנכונים על N, לכל k:
    1. מה שמעל הקו לא זז
    2. בבלוק, האיברים הפותחים עולים
    3. בבלוק, שורות האפס בתחתית
    4. אם כל הבלוק היה אפס בעמודות ≤ c, הוא נשאר אפס שם

    סעיף 4 הוא זה שהיה חסר: בלעדיו אי אפשר לדעת שהציר של שורה k
    נשאר משמאל לצירים של השורות שמתחתיה גם אחרי הסבבים הבאים. -/
theorem Echelonizes_block {A : Type} [Field_ A] {m n : Nat}
    {k : Nat} {M N : AugMatrix A m n} (h : Echelonizes k M N) :
    (∀ i : Fin m, i.val < k → N i = M i)
  ∧ (∀ i₁ i₂ : Fin m, k ≤ i₁.val → i₁ < i₂ →
       ∀ j₁ j₂ : Fin (n + 1),
         IsLeadingIndex (N i₁) j₁ → IsLeadingIndex (N i₂) j₂ → j₁ < j₂)
  ∧ (∀ i₁ i₂ : Fin m, k ≤ i₁.val → i₁ < i₂ →
       IsZeroRow (N i₁) → IsZeroRow (N i₂))
  ∧ (∀ c : Fin (n + 1),
       (∀ i : Fin m, k ≤ i.val → ∀ j' : Fin (n + 1), j' ≤ c →
          M i j' = Field_.zero) →
       (∀ i : Fin m, k ≤ i.val → ∀ j' : Fin (n + 1), j' ≤ c →
          N i j' = Field_.zero)) := by
  sorry

/-- ובמקרה k = 0: סעיפים 2 ו-3 **הם** בדיוק הגדרת מטריצת מדרגות. -/
theorem Echelonizes_IsEchelon {A : Type} [Field_ A] {m n : Nat}
    {M N : AugMatrix A m n} (h : Echelonizes 0 M N) : IsEchelon N := by
  obtain ⟨_, hlead, hzero, _⟩ := Echelonizes_block h
  constructor
  · intro i₁ i₂ j₁ j₂ horder h₁ h₂
    exact hlead i₁ i₂ (Nat.zero_le _) horder j₁ j₂ h₁ h₂
  · intro i₁ i₂ horder hz
    exact hzero i₁ i₂ (Nat.zero_le _) horder hz

-- ------------------------------------------------------------
-- טענה 3 מתוך 3: תמיד קיימת גזירה
--
-- כאן, ורק כאן, בונים פעולות בפועל. שתי הטענות הקודמות לא רואות
-- את זה בכלל.
-- ------------------------------------------------------------

/-- הליבה הקלאסית של כל הפרק: אם תכונה מתקיימת עבור אינדקס כלשהו,
    יש אינדקס מינימלי כזה.
    ממנה נובעים גם exists_IsLeadingIndex וגם exists_first_nonzero_column. -/
theorem exists_min_index {n : Nat} (P : Fin n → Prop) (h : ∃ j : Fin n, P j) :
    ∃ j : Fin n, P j ∧ ∀ k : Fin n, k < j → ¬ P k := by
  sorry

/-- צעד 1א: "בוחרים את העמודה הראשונה של המטריצה שיש בה איבר שונה מ-0",
    בתוך הבלוק שמתחת לקו. -/
theorem exists_first_nonzero_column {A : Type} [Field_ A] {m n : Nat}
    (M : AugMatrix A m n) (k : Nat)
    (hnz : ∃ (i : Fin m) (j : Fin (n + 1)), k ≤ i.val ∧ M i j ≠ Field_.zero) :
    ∃ j : Fin (n + 1),
      (∃ i : Fin m, k ≤ i.val ∧ M i j ≠ Field_.zero) ∧
      (∀ j' : Fin (n + 1), j' < j →
         ∀ i : Fin m, k ≤ i.val → M i j' = Field_.zero) := by
  sorry

/-- צעדים 1ב ו-2 יחד: מביאים ציר לשורה k ומאפסים מתחתיו.
    זה בדיוק מה ש-round דורש, ולכן נוח לבנות אותו כחתיכה אחת.
    הסקלר שמאפס את שורה i הוא  neg (M i j * inv (M k j)). -/
theorem exists_round_step {A : Type} [Field_ A] {m n : Nat}
    (M : AugMatrix A m n) (k : Nat) (hk : k < m) (j : Fin (n + 1))
    (hcol : ∃ i : Fin m, k ≤ i.val ∧ M i j ≠ Field_.zero)
    (hleft : ∀ j' : Fin (n + 1), j' < j →
               ∀ i : Fin m, k ≤ i.val → M i j' = Field_.zero) :
    ∃ Mp : AugMatrix A m n,
      RowEquivalent M Mp ∧
      Mp ⟨k, hk⟩ j ≠ Field_.zero ∧
      (∀ i : Fin m, k ≤ i.val →
         ∀ j' : Fin (n + 1), j' < j → Mp i j' = Field_.zero) ∧
      (∀ i : Fin m, k < i.val → Mp i j = Field_.zero) := by
  sorry

/-- וההרכבה: אינדוקציה על m - k. -/
theorem exists_Echelonizes {A : Type} [Field_ A] {m n : Nat}
    (M : AugMatrix A m n) : ∃ N : AugMatrix A m n, Echelonizes 0 M N := by
  sorry

-- ------------------------------------------------------------
-- ומכאן משפט 1.10.5 הוא הרכבה של השלושה
-- ------------------------------------------------------------

theorem exists_echelon {A : Type} [Field_ A] {m n : Nat}
    (M : AugMatrix A m n) :
    ∃ N : AugMatrix A m n, IsEchelon N ∧ RowEquivalent M N := by
  obtain ⟨N, hEch⟩ := exists_Echelonizes M
  apply Exists.intro N
  constructor
  · exact Echelonizes_IsEchelon hEch
  · exact Echelonizes_RowEquivalent hEch

/-- הניסוח של הספר במונחי מערכות (הגדרה 1.10.3). -/
theorem every_system_CanBeEchelonized {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) : CanBeEchelonized sys := by
  sorry

-- ============================================================
-- מחיקת העמודה האחרונה
--
-- שתי בעיות שסימנו נפתרות כאן:
--   1. הפער בין מטריצת המקדמים (n עמודות) למורחבת (n+1)
--   2. ההגבלה של RowEquivalent לרוחב n+1
-- ============================================================

/-- מחיקת העמודה האחרונה של מטריצה. -/
def dropLastColumn {A : Type} {m n : Nat} (M : Matrix_ A m (n + 1)) : Matrix_ A m n :=
  fun i j => M i (Fin.castSucc j)

/-- מטריצת המקדמים של מערכת היא בדיוק המטריצה המורחבת שלה
    בלי העמודה האחרונה. -/
theorem coefficientMatrix_eq_dropLastColumn {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) :
    coefficientMatrix sys = dropLastColumn (augmentedMatrix sys) := by
  funext i j
  unfold coefficientMatrix
  unfold dropLastColumn
  unfold augmentedMatrix
  show (sys.equations i).a j
      = (if h : j.val < n then (sys.equations i).a ⟨j.val, h⟩
         else (sys.equations i).b)
  rw [dif_pos j.isLt]

/-- מחיקת העמודה האחרונה משמרת דירוג.

    הנקודה העדינה: שורה אחת עלולה להפוך לשורת אפס - זו שהאיבר
    הפותח שלה ישב בדיוק בעמודה האחרונה. אבל האיברים הפותחים עולים
    ממש כשיורדים בשורות, ועמודה n היא הגדולה ביותר האפשרית, ולכן
    השורה הזאת היא בהכרח האחרונה שאינה שורת אפס. היא הופכת לשורת
    אפס בדיוק במקום הנכון.

    ההוכחה נשענת על exists_IsLeadingIndex (שורה היא או שורת אפס או
    שיש לה איבר פותח), ולכן בסופו של דבר על exists_min_index. -/
theorem IsEchelon_dropLastColumn {A : Type} [Field_ A] {m n : Nat}
    (M : Matrix_ A m (n + 1)) (h : IsEchelon M) :
    IsEchelon (dropLastColumn M) := by
  sorry

/-- מטריצה ברוחב 0 היא מטריצת מדרגות: אין בה עמודות, ולכן אין
    בשום שורה איבר פותח, וכל שורה היא שורת אפס. שני התנאים ריקניים. -/
theorem IsEchelon_of_width_zero {A : Type} [Field_ A] {m : Nat}
    (M : Matrix_ A m 0) : IsEchelon M := by
  constructor
  · intro i₁ i₂ j₁ j₂ _ _ _
    exact Fin.elim0 j₁
  · intro i₁ i₂ _ _ j
    exact Fin.elim0 j

/-- וכאן המנגנון שפותר את ההגבלה על הרוחב.

    Matrix_ A m k מול AugMatrix A m n = Matrix_ A m (n+1) נראה כמו
    בעיה של טיפוסים תלויים, אבל אין צורך בשום המרה: אחרי
    cases k with | succ n, הטיפוס Matrix_ A m (n+1) הוא **מילולית**
    AugMatrix A m n, והקריאה פשוט עוברת.

    הכלל: כשנתקעים על k מול n+1 - cases על k, לא cast. -/
theorem exists_echelon_general {A : Type} [Field_ A] {m k : Nat}
    (M : Matrix_ A m k) : ∃ N : Matrix_ A m k, IsEchelon N := by
  cases k with
  | zero =>
      apply Exists.intro M
      exact IsEchelon_of_width_zero M
  | succ n =>
      obtain ⟨N, hEchelon, _⟩ := exists_echelon M
      apply Exists.intro N
      exact hEchelon
