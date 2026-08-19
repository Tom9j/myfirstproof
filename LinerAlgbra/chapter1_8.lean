import LinerAlgbra.chapter1_7

-- Chapter 1.8: row-equivalent matrices

-- Read an augmented matrix as a general linear system.
-- The first n entries of every row are the coefficients, and the last entry is b.
def systemFromAugmentedMatrix {A : Type} [Field_ A] {m n : Nat}
    (matrix : Ntuple (Ntuple A (n + 1)) m) :
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
    (matrix : Ntuple (Ntuple A (n + 1)) m) :
    Ntuple (Ntuple A (n + 1)) m :=
  AugmentedMatrix
    (applyElementaryOperation operation
      (systemFromAugmentedMatrix matrix))


-- Reuse the finite sequence already defined for linear systems.
def applyMatrixSequence
    {A : Type} [Field_ A] {m n : Nat}
    (length : Nat)
    (operations : Ntuple (ElementaryOperation A m n) length)
    (initialMatrix : Ntuple (Ntuple A (n + 1)) m) :
    Ntuple (Ntuple A (n + 1)) m :=
  AugmentedMatrix
    (applySequence length operations
      (systemFromAugmentedMatrix initialMatrix))

-- Two augmented matrices are row equivalent when one is obtained from the other
-- by a finite sequence of elementary row operations.
def RowEquivalent
    {A : Type} [Field_ A] {m n : Nat}
    (firstMatrix secondMatrix : Ntuple (Ntuple A (n + 1)) m) : Prop :=
  ∃ length : Nat,
    ∃ operations : Ntuple (ElementaryOperation A m n) length,
      secondMatrix = applyMatrixSequence length operations firstMatrix

theorem systemFromAugmentedMatrix_AugmentedMatrix
    {A : Type} [Field_ A] {m n : Nat}
    (system : LinearSystem A m n) :
    systemFromAugmentedMatrix (AugmentedMatrix system) = system := by
  cases system with
  | mk equations =>
      simp [systemFromAugmentedMatrix, AugmentedMatrix]

theorem AugmentedMatrix_systemFromAugmentedMatrix
    {A : Type} [Field_ A] {m n : Nat}
    (matrix : Ntuple (Ntuple A (n + 1)) m) :
    AugmentedMatrix (systemFromAugmentedMatrix matrix) = matrix := by
  funext row column
  unfold AugmentedMatrix systemFromAugmentedMatrix
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
    (matrix : Ntuple (Ntuple A (n + 1)) m) :
    applyMatrixSequence (firstLength + secondLength)
        (Fin.append firstOperations secondOperations) matrix =
      applyMatrixSequence secondLength secondOperations
        (applyMatrixSequence firstLength firstOperations matrix) := by
  unfold applyMatrixSequence
  rw [applySequence_append]
  rw [systemFromAugmentedMatrix_AugmentedMatrix]

theorem applyMatrix_inverseElementaryOperation
    {A : Type} [Field_ A] {m n : Nat}
    (operation : ElementaryOperation A m n)
    (matrix : Ntuple (Ntuple A (n + 1)) m) :
    applyMatrixElementaryOperation (inverseElementaryOperation operation)
        (applyMatrixElementaryOperation operation matrix) = matrix := by
  unfold applyMatrixElementaryOperation
  rw [systemFromAugmentedMatrix_AugmentedMatrix]
  rw [apply_inverseElementaryOperation]
  exact AugmentedMatrix_systemFromAugmentedMatrix matrix

theorem applyMatrixSequence_zero
    {A : Type} [Field_ A] {m n : Nat}
    (operations : Ntuple (ElementaryOperation A m n) 0)
    (matrix : Ntuple (Ntuple A (n + 1)) m) :
    applyMatrixSequence 0 operations matrix = matrix := by
  unfold applyMatrixSequence applySequence
  exact AugmentedMatrix_systemFromAugmentedMatrix matrix

theorem applyMatrixSequence_succ
    {A : Type} [Field_ A] {m n k : Nat}
    (operations : Ntuple (ElementaryOperation A m n) (k + 1))
    (matrix : Ntuple (Ntuple A (n + 1)) m) :
    applyMatrixSequence (k + 1) operations matrix =
      applyMatrixElementaryOperation
        (operations ⟨k, Nat.lt_succ_self k⟩)
        (applyMatrixSequence k
          (fun index => operations ⟨index.val,
            Nat.lt_trans index.isLt (Nat.lt_succ_self k)⟩)
          matrix) := by
  unfold applyMatrixSequence applyMatrixElementaryOperation
  rw [systemFromAugmentedMatrix_AugmentedMatrix]
  rw [applySequence]

theorem RowEquivalent_refl
    {A : Type} [Field_ A] {m n : Nat}
    (matrix : Ntuple (Ntuple A (n + 1)) m) :
    RowEquivalent matrix matrix := by
  refine ⟨0, fun index => Fin.elim0 index, ?_⟩
  exact (applyMatrixSequence_zero _ matrix).symm

theorem RowEquivalent_single
    {A : Type} [Field_ A] {m n : Nat}
    (operation : ElementaryOperation A m n)
    (matrix : Ntuple (Ntuple A (n + 1)) m) :
    RowEquivalent matrix (applyMatrixElementaryOperation operation matrix) := by
  refine ⟨1, fun _ => operation, ?_⟩
  rw [applyMatrixSequence_succ]
  rw [applyMatrixSequence_zero]

theorem RowEquivalent_trans
    {A : Type} [Field_ A] {m n : Nat}
    {firstMatrix secondMatrix thirdMatrix :
      Ntuple (Ntuple A (n + 1)) m}
    (firstToSecond : RowEquivalent firstMatrix secondMatrix)
    (secondToThird : RowEquivalent secondMatrix thirdMatrix) :
    RowEquivalent firstMatrix thirdMatrix := by
  obtain ⟨firstLength, firstOperations, firstEquality⟩ := firstToSecond
  obtain ⟨secondLength, secondOperations, secondEquality⟩ := secondToThird
  refine ⟨firstLength + secondLength,
    Fin.append firstOperations secondOperations, ?_⟩
  rw [applyMatrixSequence_append]
  rw [← firstEquality]
  exact secondEquality

theorem RowEquivalent_inverse_step
    {A : Type} [Field_ A] {m n : Nat}
    (operation : ElementaryOperation A m n)
    (matrix : Ntuple (Ntuple A (n + 1)) m) :
    RowEquivalent (applyMatrixElementaryOperation operation matrix) matrix := by
  have inverseStep := RowEquivalent_single
    (inverseElementaryOperation operation)
    (applyMatrixElementaryOperation operation matrix)
  rw [applyMatrix_inverseElementaryOperation] at inverseStep
  exact inverseStep

theorem RowEquivalent_symm
    {A : Type} [Field_ A] {m n : Nat}
    {firstMatrix secondMatrix : Ntuple (Ntuple A (n + 1)) m}
    (equivalent : RowEquivalent firstMatrix secondMatrix) :
    RowEquivalent secondMatrix firstMatrix := by
  obtain ⟨length, operations, equality⟩ := equivalent
  subst secondMatrix
  induction length with
  | zero =>
      rw [applyMatrixSequence_zero]
      exact RowEquivalent_refl firstMatrix
  | succ k inductionHypothesis =>
      let previousOperations : Ntuple (ElementaryOperation A m n) k :=
        fun index => operations ⟨index.val,
          Nat.lt_trans index.isLt (Nat.lt_succ_self k)⟩
      let lastOperation : ElementaryOperation A m n :=
        operations ⟨k, Nat.lt_succ_self k⟩
      let beforeLast :=
        applyMatrixSequence k previousOperations firstMatrix
      have lastBack :
          RowEquivalent
            (applyMatrixElementaryOperation lastOperation beforeLast)
            beforeLast :=
        RowEquivalent_inverse_step lastOperation beforeLast
      have previousBack : RowEquivalent beforeLast firstMatrix :=
        inductionHypothesis previousOperations
      rw [applyMatrixSequence_succ]
      exact RowEquivalent_trans lastBack previousBack

theorem RowEquivalent_equivalence
    {A : Type} [Field_ A] {m n : Nat} :
    Equivalence (@RowEquivalent A _ m n) :=
  ⟨RowEquivalent_refl, RowEquivalent_symm, RowEquivalent_trans⟩
