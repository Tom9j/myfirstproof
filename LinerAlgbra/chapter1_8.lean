import LinerAlgbra.chapter1_7

-- Chapter 1.8: row-equivalent matrices

-- Read an augmented matrix as a general linear system.
-- The first n entries of every row are the coefficients, and the last entry is b.
def systemFromAugmentedMatrix {A : Type} [Field_ A] {m n : Nat}
    (matrix : AugMatrix A m n) :
    LinearSystem A m n :=
  { equations := fun row =>
      { a := fun column =>
          matrix row
            ⟨column.val, Nat.lt_trans column.isLt (Nat.lt_succ_self n)⟩
        b := matrix row ⟨n, Nat.lt_succ_self n⟩ } }

-- Reuse the elementary operation already defined for linear systems.
def applyMatrixElementaryOperation
    {A : Type} [Field_ A] {m n : Nat}
    (operation : ElementaryOperation A m n)
    (matrix : AugMatrix A m n) :
    AugMatrix A m n :=
  augmentedMatrix
    (applyElementaryOperation operation
      (systemFromAugmentedMatrix matrix))


-- Reuse the finite sequence already defined for linear systems.
def applyMatrixSequence
    {A : Type} [Field_ A] {m n : Nat}
    (length : Nat)
    (operations : Ntuple (ElementaryOperation A m n) length)
    (initialMatrix : AugMatrix A m n) :
    AugMatrix A m n :=
  augmentedMatrix
    (applySequence length operations
      (systemFromAugmentedMatrix initialMatrix))

theorem systemFromAugmentedMatrix_augmentedMatrix
    {A : Type} [Field_ A] {m n : Nat}
    (system : LinearSystem A m n) :
    systemFromAugmentedMatrix (augmentedMatrix system) = system := by
  cases system with
  | mk equations =>
      simp [systemFromAugmentedMatrix, augmentedMatrix]

theorem augmentedMatrix_systemFromAugmentedMatrix
    {A : Type} [Field_ A] {m n : Nat}
    (matrix : AugMatrix A m n) :
    augmentedMatrix (systemFromAugmentedMatrix matrix) = matrix := by
  funext row column
  unfold augmentedMatrix systemFromAugmentedMatrix
  split
  · rfl
  · have columnIsLast : column.val = n := by omega
    have columnEquality :
        column = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext columnIsLast
    rw [columnEquality]

noncomputable def inverseElementaryOperation
    {A : Type} [Field_ A] {m n : Nat} :
    ElementaryOperation A m n → ElementaryOperation A m n
  | .switchRows row1 row2 => .switchRows row1 row2
  | .scaleRow row scalar nonzero =>
      .scaleRow row (inv scalar nonzero) (by
        intro inverseIsZero
        have cancel := (MulInverseCancel scalar nonzero).left
        rw [inverseIsZero, (MulByZeroIsZero scalar).left] at cancel
        exact Field_.zero_neq_one cancel)
  | .addRow targetRow sourceRow scalar differentRows =>
      .addRow targetRow sourceRow (neg scalar) differentRows

theorem apply_inverseElementaryOperation
    {A : Type} [Field_ A] {m n : Nat}
    (operation : ElementaryOperation A m n)
    (system : LinearSystem A m n) :
    applyElementaryOperation (inverseElementaryOperation operation)
        (applyElementaryOperation operation system) = system := by
  cases operation with
  | switchRows row1 row2 =>
      cases system with
      | mk equations =>
          simp only [inverseElementaryOperation, applyElementaryOperation, switch]
          congr 1
          funext row
          by_cases rowIsFirst : row = row1 <;>
            by_cases rowIsSecond : row = row2 <;>
            simp [rowIsFirst, rowIsSecond] <;> aesop
  | scaleRow row scalar nonzero =>
      cases system with
      | mk equations =>
          simp only [inverseElementaryOperation, applyElementaryOperation, scaleRow]
          congr 1
          funext currentRow
          by_cases isScaledRow : currentRow = row
          · subst currentRow
            simp only [if_pos]
            congr 1
            · funext column
              unfold Ntuple_smul
              rw [← Field_.mul_assoc]
              rw [(MulInverseCancel scalar nonzero).right]
              rw [(Field_.mul_neut _).left]
            · rw [← Field_.mul_assoc]
              rw [(MulInverseCancel scalar nonzero).right]
              rw [(Field_.mul_neut _).left]
          · simp [isScaledRow]
  | addRow targetRow sourceRow scalar differentRows =>
      cases system with
      | mk equations =>
          have sourceDifferent : sourceRow ≠ targetRow := by
            intro equality
            exact differentRows equality.symm
          have cancelTerm (x : A) :
              Field_.add (Field_.mul scalar x) (Field_.mul (neg scalar) x) =
                Field_.zero := by
            rw [← FieldDistributiveLaw.right]
            rw [(AddInverseCancel scalar).left]
            rw [(MulByZeroIsZero x).right]
          simp only [inverseElementaryOperation, applyElementaryOperation, addRow]
          congr 1
          funext currentRow
          by_cases isTargetRow : currentRow = targetRow
          · subst currentRow
            simp only [if_pos, if_neg sourceDifferent]
            congr 1
            · funext column
              unfold Ntuple_add Ntuple_smul
              rw [Field_.add_assoc]
              rw [cancelTerm]
              rw [(Field_.add_neut _).right]
            · rw [Field_.add_assoc]
              rw [cancelTerm]
              rw [(Field_.add_neut _).right]
          · simp [isTargetRow]

theorem applySequence_append
    {A : Type} [Field_ A] {m n firstLength secondLength : Nat}
    (firstOperations : Ntuple (ElementaryOperation A m n) firstLength)
    (secondOperations : Ntuple (ElementaryOperation A m n) secondLength)
    (system : LinearSystem A m n) :
    applySequence (firstLength + secondLength)
        (Fin.append firstOperations secondOperations) system =
      applySequence secondLength secondOperations
        (applySequence firstLength firstOperations system) := by
  induction secondLength with
  | zero =>
      have appendEmpty :
          Fin.append firstOperations secondOperations = firstOperations := by
        funext index
        simpa using Fin.append_left firstOperations secondOperations index
      rw [appendEmpty]
      rfl
  | succ k inductionHypothesis =>
      let secondPrefix : Ntuple (ElementaryOperation A m n) k :=
        fun index => secondOperations ⟨index.val,
          Nat.lt_trans index.isLt (Nat.lt_succ_self k)⟩
      let combinedPrefix :
          Ntuple (ElementaryOperation A m n) (firstLength + k) :=
        fun index => (Fin.append firstOperations secondOperations)
          ⟨index.val, Nat.lt_trans index.isLt
            (Nat.lt_succ_self (firstLength + k))⟩
      let combinedLast : ElementaryOperation A m n :=
        (Fin.append firstOperations secondOperations)
          ⟨firstLength + k, by omega⟩
      have prefixEquality :
          combinedPrefix = Fin.append firstOperations secondPrefix := by
        funext index
        refine Fin.addCases ?_ ?_ index
        · intro leftIndex
          have indexEquality :
              (⟨(Fin.castAdd k leftIndex).val, by omega⟩ :
                  Fin (firstLength + (k + 1))) =
                Fin.castAdd (k + 1) leftIndex := by
            apply Fin.ext
            rfl
          simp only [combinedPrefix]
          rw [indexEquality, Fin.append_left, Fin.append_left]
        · intro rightIndex
          have indexEquality :
              (⟨(Fin.natAdd firstLength rightIndex).val, by omega⟩ :
                  Fin (firstLength + (k + 1))) =
                Fin.natAdd firstLength rightIndex.castSucc := by
            apply Fin.ext
            rfl
          simp only [combinedPrefix]
          rw [indexEquality, Fin.append_right, Fin.append_right]
          apply congrArg secondOperations
          apply Fin.ext
          rfl
      have lastEquality :
          combinedLast = secondOperations ⟨k, Nat.lt_succ_self k⟩ := by
        have indexEquality :
            (⟨firstLength + k, by omega⟩ :
                Fin (firstLength + (k + 1))) =
              Fin.natAdd firstLength (Fin.last k) := by
          apply Fin.ext
          rfl
        simp only [combinedLast]
        rw [indexEquality, Fin.append_right]
        rfl
      unfold applySequence
      change applyElementaryOperation combinedLast
          (applySequence (firstLength + k) combinedPrefix system) =
        applyElementaryOperation
          (secondOperations ⟨k, Nat.lt_succ_self k⟩)
          (applySequence k secondPrefix
            (applySequence firstLength firstOperations system))
      rw [prefixEquality, lastEquality, inductionHypothesis secondPrefix]

theorem applyMatrixSequence_append
    {A : Type} [Field_ A] {m n firstLength secondLength : Nat}
    (firstOperations : Ntuple (ElementaryOperation A m n) firstLength)
    (secondOperations : Ntuple (ElementaryOperation A m n) secondLength)
    (matrix : AugMatrix A m n) :
    applyMatrixSequence (firstLength + secondLength)
        (Fin.append firstOperations secondOperations) matrix =
      applyMatrixSequence secondLength secondOperations
        (applyMatrixSequence firstLength firstOperations matrix) := by
  unfold applyMatrixSequence
  rw [applySequence_append]
  rw [systemFromAugmentedMatrix_augmentedMatrix]

theorem applyMatrix_inverseElementaryOperation
    {A : Type} [Field_ A] {m n : Nat}
    (operation : ElementaryOperation A m n)
    (matrix : AugMatrix A m n) :
    applyMatrixElementaryOperation (inverseElementaryOperation operation)
        (applyMatrixElementaryOperation operation matrix) = matrix := by
  unfold applyMatrixElementaryOperation
  rw [systemFromAugmentedMatrix_augmentedMatrix]
  rw [apply_inverseElementaryOperation]
  exact augmentedMatrix_systemFromAugmentedMatrix matrix

theorem applyMatrixSequence_zero
    {A : Type} [Field_ A] {m n : Nat}
    (operations : Ntuple (ElementaryOperation A m n) 0)
    (matrix : AugMatrix A m n) :
    applyMatrixSequence 0 operations matrix = matrix := by
  unfold applyMatrixSequence applySequence
  exact augmentedMatrix_systemFromAugmentedMatrix matrix

theorem applyMatrixSequence_succ
    {A : Type} [Field_ A] {m n k : Nat}
    (operations : Ntuple (ElementaryOperation A m n) (k + 1))
    (matrix : AugMatrix A m n) :
    applyMatrixSequence (k + 1) operations matrix =
      applyMatrixElementaryOperation
        (operations ⟨k, Nat.lt_succ_self k⟩)
        (applyMatrixSequence k
          (fun index => operations ⟨index.val,
            Nat.lt_trans index.isLt (Nat.lt_succ_self k)⟩)
          matrix) := by
  unfold applyMatrixSequence applyMatrixElementaryOperation
  rw [systemFromAugmentedMatrix_augmentedMatrix]
  rw [applySequence]


-- ============================================================
-- 1.8.1  שקילות־שורה
-- הגדרה 1.8.1 בספר: A שקולת-שורה ל-B אם יש סדרה סופית של
-- פעולות שורה שמובילה מ-A ל-B.
--
-- מנוסח כאן כטיפוס אינדוקטיבי: הסגור הרפלקסיבי-טרנזיטיבי של
-- "צעד אחד". השקילות לניסוח של הספר, עם סדרה מפורשת, מוכחת
-- למטה בשני הכיוונים.
--
-- המטריצה הראשונה היא *פרמטר* (לפני הנקודתיים) והשנייה
-- *אינדקס* (אחרי הנקודתיים): induction מכליל אינדקסים בלבד,
-- ולכן הנחות אחרות שמדברות על הראשונה לא נגררות למוטיב.
-- ============================================================

inductive RowEquivalent {A : Type} [Field_ A] {m n : Nat}
    (firstMatrix : AugMatrix A m n) : AugMatrix A m n → Prop
  | refl : RowEquivalent firstMatrix firstMatrix
  | step {middleMatrix : AugMatrix A m n}
      (operation : ElementaryOperation A m n)
      (h : RowEquivalent firstMatrix middleMatrix) :
      RowEquivalent firstMatrix
        (applyMatrixElementaryOperation operation middleMatrix)

/-- צעד בודד קדימה. -/
theorem RowEquivalent_single {A : Type} [Field_ A] {m n : Nat}
    (operation : ElementaryOperation A m n) (matrix : AugMatrix A m n) :
    RowEquivalent matrix (applyMatrixElementaryOperation operation matrix) :=
  RowEquivalent.step operation RowEquivalent.refl

/-- צעד בודד אחורה, דרך הפעולה ההופכית. -/
theorem RowEquivalent_inverse_step {A : Type} [Field_ A] {m n : Nat}
    (operation : ElementaryOperation A m n) (matrix : AugMatrix A m n) :
    RowEquivalent (applyMatrixElementaryOperation operation matrix) matrix := by
  have h : RowEquivalent (applyMatrixElementaryOperation operation matrix)
      (applyMatrixElementaryOperation (inverseElementaryOperation operation)
        (applyMatrixElementaryOperation operation matrix)) :=
    RowEquivalent_single (inverseElementaryOperation operation)
      (applyMatrixElementaryOperation operation matrix)
  rw [applyMatrix_inverseElementaryOperation] at h
  exact h

theorem RowEquivalent_trans {A : Type} [Field_ A] {m n : Nat}
    (firstMatrix secondMatrix thirdMatrix : AugMatrix A m n)
    (firstToSecond : RowEquivalent firstMatrix secondMatrix)
    (secondToThird : RowEquivalent secondMatrix thirdMatrix) :
    RowEquivalent firstMatrix thirdMatrix := by
  induction secondToThird with
  | refl =>
      exact firstToSecond
  | step operation hMiddle ih =>
      exact RowEquivalent.step operation ih

theorem RowEquivalent_symm {A : Type} [Field_ A] {m n : Nat}
    (firstMatrix secondMatrix : AugMatrix A m n)
    (h : RowEquivalent firstMatrix secondMatrix) :
    RowEquivalent secondMatrix firstMatrix := by
  induction h with
  | refl =>
      exact RowEquivalent.refl
  | step operation hMiddle ih =>
      exact RowEquivalent_trans _ _ _
        (RowEquivalent_inverse_step operation _) ih

theorem RowEquivalent_equivalence {A : Type} [Field_ A] {m n : Nat} :
    Equivalence (fun (M N : AugMatrix A m n) => RowEquivalent M N) :=
  { refl  := fun _M => RowEquivalent.refl
    symm  := fun {M N} h => RowEquivalent_symm M N h
    trans := fun {M N P} h₁ h₂ => RowEquivalent_trans M N P h₁ h₂ }

-- ============================================================
-- 1.8.2  השקילות לניסוח של הספר, עם סדרה סופית מפורשת
-- ============================================================

/-- הוספת פעולה בסוף סדרה. -/
def appendOp {A : Type} [Field_ A] {m n length : Nat}
    (operations : Ntuple (ElementaryOperation A m n) length)
    (operation : ElementaryOperation A m n) :
    Ntuple (ElementaryOperation A m n) (length + 1) :=
  fun index =>
    if hi : index.val < length then operations ⟨index.val, hi⟩ else operation

theorem appendOp_last {A : Type} [Field_ A] {m n length : Nat}
    (operations : Ntuple (ElementaryOperation A m n) length)
    (operation : ElementaryOperation A m n) :
    appendOp operations operation ⟨length, Nat.lt_succ_self length⟩ = operation := by
  show (if hi : length < length then operations ⟨length, hi⟩ else operation) = operation
  rw [dif_neg (Nat.lt_irrefl length)]

theorem appendOp_init {A : Type} [Field_ A] {m n length : Nat}
    (operations : Ntuple (ElementaryOperation A m n) length)
    (operation : ElementaryOperation A m n) :
    (fun index : Fin length =>
      appendOp operations operation
        ⟨index.val, Nat.lt_trans index.isLt (Nat.lt_succ_self length)⟩) = operations := by
  funext index
  show (if hi : index.val < length then operations ⟨index.val, hi⟩ else operation)
      = operations index
  rw [dif_pos index.isLt]

/-- כל סדרה סופית של פעולות מייצרת מטריצה שקולת־שורה. -/
theorem RowEquivalent_applyMatrixSequence {A : Type} [Field_ A] {m n : Nat} :
    ∀ (length : Nat) (operations : Ntuple (ElementaryOperation A m n) length)
      (matrix : AugMatrix A m n),
      RowEquivalent matrix (applyMatrixSequence length operations matrix) := by
  intro length
  induction length with
  | zero =>
      intro operations matrix
      rw [applyMatrixSequence_zero]
      exact RowEquivalent.refl
  | succ k ih =>
      intro operations matrix
      rw [applyMatrixSequence_succ]
      exact RowEquivalent.step (operations ⟨k, Nat.lt_succ_self k⟩)
        (ih (fun index => operations
          ⟨index.val, Nat.lt_trans index.isLt (Nat.lt_succ_self k)⟩) matrix)

/-- ולהפך. שני המשפטים יחד מראים שההגדרה האינדוקטיבית שקולה
    להגדרה 1.8.1 בספר. -/
theorem applyMatrixSequence_of_RowEquivalent {A : Type} [Field_ A] {m n : Nat}
    (firstMatrix secondMatrix : AugMatrix A m n)
    (h : RowEquivalent firstMatrix secondMatrix) :
    ∃ (length : Nat) (operations : Ntuple (ElementaryOperation A m n) length),
      secondMatrix = applyMatrixSequence length operations firstMatrix := by
  induction h with
  | refl =>
      apply Exists.intro 0
      apply Exists.intro (fun index : Fin 0 => Fin.elim0 index)
      rw [applyMatrixSequence_zero]
  | step operation hMiddle ih =>
      obtain ⟨length, operations, hops⟩ := ih
      apply Exists.intro (length + 1)
      apply Exists.intro (appendOp operations operation)
      rw [applyMatrixSequence_succ]
      rw [appendOp_last]
      rw [appendOp_init]
      rw [hops]

-- ============================================================
-- 1.8.3  המסקנה של הסעיף (הספר, עמ' 70)
-- "אם שתי מטריצות הן שקולות־שורה, אז המערכות הלינאריות
--  שהן מייצגות הן שקולות."
-- ============================================================

theorem RowEquivalent_implies_AreEquivalent {A : Type} [Field_ A] {m n : Nat}
    (firstMatrix secondMatrix : AugMatrix A m n)
    (h : RowEquivalent firstMatrix secondMatrix) :
    AreEquivalent (systemFromAugmentedMatrix firstMatrix)
                  (systemFromAugmentedMatrix secondMatrix) := by
  induction h with
  | refl =>
      exact AreEquivalent_refl (systemFromAugmentedMatrix firstMatrix)
  | step operation hMiddle ih =>
      unfold applyMatrixElementaryOperation
      rw [systemFromAugmentedMatrix_augmentedMatrix]
      exact AreEquivalent_trans _ _ _ ih
        (elementaryOperation_equivalent operation _)
