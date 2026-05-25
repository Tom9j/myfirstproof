import LinerAlgbra.chapter1_2

-- ==========================================
-- הגדרות בסיסיות: וקטור, שוויון
-- ==========================================

def NTuple (A : Type) (n : Nat) := Fin n → A

def NTuple_Equal {A : Type} {n : Nat} (u v : NTuple A n) : Prop :=
  ∀ i, u i = v i

-- ==========================================
-- חיבור וקטורים
-- ==========================================

def NTuple_add {A : Type} [Field_ A] {n : Nat} : Operation (NTuple A n) (NTuple A n) (NTuple A n) :=
  fun u v => fun i => Field_.add (u i) (v i)

theorem NTuple_add_Is_Closed {A : Type} [Field_ A] {n : Nat}: IsClosedOp (NTuple A n) NTuple_add := by
  unfold IsClosedOp
  intro a b
  use (NTuple_add a b)

theorem NTuple_add_Is_Assoc {A : Type} [Field_ A] {n : Nat} : IsAssociativeOp (NTuple A n) NTuple_add := by
  unfold IsAssociativeOp
  intro a b c
  funext i
  unfold NTuple_add
  rw [Field_.add_assoc]

theorem NTuple_add_Is_Comm {A : Type} [Field_ A] {n : Nat} : IsCommutativeOp (NTuple A n) NTuple_add := by
  unfold IsCommutativeOp
  intro a b
  unfold NTuple_add
  funext i
  rw[Field_.add_comm]

def NTuple_zero {A : Type} [Field_ A] {n : Nat} : NTuple A n :=
  fun _ => Field_.zero

theorem NTuple_add_zero {A : Type} [Field_ A] {n : Nat}: IsNeutralElement (NTuple A n) (NTuple_add) (NTuple_zero) := by
  unfold IsNeutralElement
  intro a
  unfold NTuple_add NTuple_zero
  apply And.intro
  funext i
  rw [(Field_.add_neut (a i)).left]
  funext i
  rw [(Field_.add_neut (a i)).right]

theorem NTuple_all_element_has_neg {A : Type} [Field_ A] {n : Nat} : AllElementsHaveInverse (NTuple A n) (NTuple_add) NTuple_zero NTuple_add_zero := by
  unfold AllElementsHaveInverse
  intro a
  unfold IsInverseElement
  use (fun i => neg (a i))
  unfold NTuple_add NTuple_zero
  apply And.intro
  funext i
  rw[(AddInverseCancel (a i)).left]
  funext i
  rw[(AddInverseCancel (a i)).right]

-- ==========================================
-- כפל בסקלר
-- ==========================================

def NTuple_smul {A : Type} [Field_ A] {n : Nat} : Operation A (NTuple A n) (NTuple A n) :=
  fun c v => fun i => Field_.mul c (v i)

theorem NTuple_smul_on_zero {A : Type} [Field_ A] {n : Nat} (v : NTuple A n) : NTuple_smul Field_.zero v = NTuple_zero := by
  funext i
  unfold NTuple_smul NTuple_zero
  rw [(MulByZeroIsZero (v i)).right]

theorem NTuple_smul_mulbyone {A : Type} [Field_ A] {n : Nat} (v : NTuple A n) : NTuple_smul Field_.one v = v := by
  unfold NTuple_smul
  funext i
  rw[(Field_.mul_neut (v i)).left]

noncomputable def NTuple_neg {A : Type} [Field_ A] {n : Nat} (v : NTuple A n) : NTuple A n :=
  fun i => neg (v i)

theorem NTuple_smul_mulbynegone {A : Type} [Field_ A] {n : Nat} (v : NTuple A n) : NTuple_smul (neg (Field_.one)) v = (NTuple_neg v) := by
  unfold NTuple_smul NTuple_neg
  funext i
  rw[(OneNegTimesEqNeg (v i)).left]

-- 1. חוק הקיבוציות המדויק לכפל בסקלר: (a * b) * v = a * (b * v)
theorem NTuple_smul_assoc_true {A : Type} [Field_ A] {n : Nat} (a b : A) (v : NTuple A n) :
  NTuple_smul (Field_.mul a b) v = NTuple_smul a (NTuple_smul b v) := by
  unfold NTuple_smul
  funext i
  rw [Field_.mul_assoc]

-- 2. חילוף סקלרים: כפל ב-a ואז ב-b שווה לכפל ב-b ואז ב-a
theorem NTuple_smul_scalars_comm {A : Type} [Field_ A] {n : Nat} (a b : A) (v : NTuple A n) :
  NTuple_smul b (NTuple_smul a v) = NTuple_smul a (NTuple_smul b v) := by
  unfold NTuple_smul
  funext i
  rw [Field_.mul_comm a (v i)]
  rw [←Field_.mul_assoc b (v i) a]
  rw [Field_.mul_comm]

-- ==========================================
-- חוקי הפילוג
-- ==========================================

-- פילוג משמאל (סקלר כפול סכום וקטורים)
theorem NTuple_smul_distrib_left {A : Type} [Field_ A] {n : Nat} (c : A) (u v : NTuple A n) :
  NTuple_smul c (NTuple_add u v) = NTuple_add (NTuple_smul c u) (NTuple_smul c v) := by
  unfold NTuple_smul NTuple_add
  funext i
  exact Field_.distribLeft c (u i) (v i)

-- פילוג מימין (סכום סקלרים כפול וקטור)
theorem NTuple_smul_distrib_right {A : Type} [Field_ A] {n : Nat} (a b : A) (v : NTuple A n) :
  NTuple_smul (Field_.add a b) v = NTuple_add (NTuple_smul a v) (NTuple_smul b v) := by
  unfold NTuple_smul NTuple_add
  funext i
  exact FieldDistributiveLaw.right (v i) a b

def sum_NTuple {A : Type} [Field_ A] : {n : Nat} → NTuple A n → A
  | 0, _ => Field_.zero
  | k + 1, v => Field_.add (v ⟨k, Nat.lt_succ_self k⟩)
                           (sum_NTuple (fun i => v ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩))

def NTuple_dot_product {A : Type} [Field_ A] {n : Nat} (a x : NTuple A n) : A :=
  sum_NTuple (fun i => Field_.mul (a i) (x i))

structure LinearEquation (A : Type) [Field_ A] (n : Nat) where
  a : NTuple A n
  b : A

def IsSolution {A : Type} [Field_ A] {n : Nat}
    (eq : LinearEquation A n) (x : NTuple A n) : Prop :=
  NTuple_dot_product eq.a x = eq.b

structure LinearSystem (A : Type) [Field_ A] (m n : Nat) where
  equations : NTuple (LinearEquation A n) m

def IsSystemSolution {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) (x : NTuple A n) : Prop :=
  ∀ i : Fin m, IsSolution (sys.equations i) x

def IsHomogeneous (A : Type) [Field_ A] {m n : Nat} (v : LinearSystem A m n) :=
  ∀ i : Fin m, (v.equations i).b = Field_.zero

theorem sum_NTuple_zero {A : Type} [Field_ A] (n : Nat) :
    sum_NTuple (NTuple_zero : NTuple A n) = Field_.zero := by
    induction n with
    | zero =>
    rfl
    | succ k ih =>
    unfold sum_NTuple
    have h : (NTuple_zero ⟨k, Nat.lt_succ_self k⟩ = (Field_.zero : A)) := by
      rfl
    rw[h]
    rw[(Field_.add_neut (sum_NTuple fun i => NTuple_zero ⟨↑i, _⟩)).left]
    exact ih



theorem sum_NTuple_neg {A : Type} [Field_ A] {n : Nat} (v : NTuple A n) :
    sum_NTuple (NTuple_neg v) = neg (sum_NTuple v) := by
    induction n with
    | zero =>
      unfold sum_NTuple
      conv_lhs => rw[zeronegeqzero]

    | succ k ih =>
      unfold sum_NTuple

      have ihv := ih ( fun (i : Fin k)=> v ⟨↑i,Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩)
      rw[SumOfNegEQNEGADDNEG]
      rw[←ihv]
      have h :  (NTuple_neg v ⟨k, Nat.lt_succ_self k⟩) = (neg (v ⟨k, Nat.lt_succ_self k⟩)) := by
        unfold NTuple_neg
        rfl
      rw[h]
      rfl




theorem sum_NTuple_add {A : Type} [Field_ A] {n : Nat} (u v : NTuple A n) :
    sum_NTuple (NTuple_add u v) = Field_.add (sum_NTuple u) (sum_NTuple v) := by
    unfold NTuple_add
    induction n with
    |zero =>
      unfold sum_NTuple
      rw[(Field_.add_neut Field_.zero).left]
    | succ k ih =>
      unfold sum_NTuple
      rw[Field_.add_comm (u ⟨k, _⟩) (sum_NTuple fun i => u ⟨↑i, _⟩)]
      have h : Field_.add (u ⟨k, Nat.lt_succ_self k⟩) (v ⟨k, _⟩) = ((fun i => Field_.add (u i) (v i)) ⟨k, _⟩) := rfl
      rw[←h]
      have h2 : (fun (i : Fin k) => (fun (j : Fin (k+1)) => Field_.add (u j) (v j)) ⟨↑i,Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩)
              = (fun (i : Fin k) => Field_.add (u ⟨↑i, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩) (v ⟨↑i, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩)) := by
        rfl
      rw[h2]
      let u' := (fun (i : Fin k) => u ⟨↑i, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩)
      let v' := (fun (i : Fin k) => v ⟨↑i, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩)
      have ihv := ih  u' v'
      rw[ihv]
      have hl : (fun (i : Fin k) => u ⟨↑i, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩) = u' := rfl
      have hl2 : (fun (i : Fin k) => v ⟨↑i, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩) = v' := rfl
      rw[hl]
      rw[hl2]
      rw[AddCanBeFour (sum_NTuple u') (u ⟨k, _⟩) (v ⟨k, _⟩) (sum_NTuple v')]
      rw[Field_.add_comm]


lemma dot_product_with_zero {A : Type} [Field_ A] {n : Nat}
    (v : NTuple A n) : NTuple_dot_product v NTuple_zero = Field_.zero := by
    unfold NTuple_dot_product NTuple_zero
    have h : (fun i => Field_.mul (v i) Field_.zero) = fun (anyIndex : Fin n) => Field_.zero := by
      funext i
      exact (MulByZeroIsZero (v i)).left
    rw [h]
    clear v h
    induction n with
    | zero =>
        unfold sum_NTuple
        rfl
    | succ n ih =>
        unfold sum_NTuple
        have h2 : (fun i : Fin n => (fun (bigIndex : Fin (n+1)) => (Field_.zero : A))
                  ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩) =
                  fun (anyIndex : Fin n) => (Field_.zero : A) := by
          funext i
          rfl
        rw [h2, ih]
        exact (Field_.add_neut Field_.zero).left

theorem IfxEqZeroThesEveryHomogeneouswithxHasSolution (A : Type) [Field_ A] {m n : Nat} (v : LinearSystem A m n) (h : IsHomogeneous A v) : IsSystemSolution v NTuple_zero := by
  unfold IsSystemSolution NTuple_zero
  unfold IsHomogeneous at h
  intro i
  unfold IsSolution
  have h1 : (v.equations i).b = Field_.zero := by exact (h i)
  rw[h1]
  exact dot_product_with_zero (v.equations i).a

def AreEquivalent {A : Type} [Field_ A] {m₁ m₂ n : Nat}
    (sys1 : LinearSystem A m₁ n)
    (sys2 : LinearSystem A m₂ n) : Prop :=
  ∀ x : NTuple A n, IsSystemSolution sys1 x ↔ IsSystemSolution sys2 x

def swapRows {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) (i j : Fin m) : LinearSystem A m n :=
  { equations := fun k =>
      if k = i then sys.equations j
      else if k = j then sys.equations i
      else sys.equations k }

def scaleRow {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) (i : Fin m) (c : A) : LinearSystem A m n :=
  { equations := fun k =>
      if k = i then { a := NTuple_smul c (sys.equations i).a,
                      b := Field_.mul c (sys.equations i).b }
      else sys.equations k }

def addRow {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) (i j : Fin m) (c : A) : LinearSystem A m n :=
  { equations := fun k =>
      if k = j then { a := NTuple_add (sys.equations j).a (NTuple_smul c (sys.equations i).a),
                      b := Field_.add (sys.equations j).b (Field_.mul c (sys.equations i).b) }
      else sys.equations k }

theorem swapRowsOutputIsEquivalent {A : Type} [Field_ A] {m n : Nat} (sys : LinearSystem A m n) (i j : Fin m): AreEquivalent sys (swapRows sys j i) := by
  unfold AreEquivalent
  intro x
  have unfold_eq : ∀ k : Fin m,
      (({ equations := fun k => if k = j then sys.equations i
          else if k = i then sys.equations j
          else sys.equations k } : LinearSystem A m n).equations k) =
      (if k = j then sys.equations i
       else if k = i then sys.equations j
       else sys.equations k) := fun k => rfl
  constructor
  · intro h
    unfold IsSystemSolution IsSolution swapRows
    intro k
    by_cases hki : k = i
    · rw [hki]
      rw[unfold_eq i]
      by_cases hij : i = j
      · rw [if_pos hij]
        exact h i
      · rw [if_neg hij, if_pos rfl]
        exact h j
    ·
      by_cases hkj : k = j
      .
        rw[hkj]
        rw[unfold_eq j]
        rw[if_pos rfl]
        exact h i
      .
         rw[unfold_eq k]
         rw[if_neg hkj]
         rw[if_neg hki]
         exact  h k

  · intro h
    unfold IsSystemSolution IsSolution
    unfold IsSystemSolution at h
    unfold swapRows at h
    unfold IsSolution at h
    intro k
    by_cases hki : k = i
    .
      rw[hki]
      have hk := h j
      rw[unfold_eq j] at hk
      rw[if_pos rfl] at hk
      exact hk
    .
      by_cases hkj : k = j
      .
        rw[hkj]
        have hk := h i
        rw[unfold_eq i] at hk
        by_cases hij : i = j
        · rw [if_pos hij] at hk
          rw[←hij]
          exact hk
        · rw [if_neg hij, if_pos rfl] at hk
          exact hk
      .
        have hk := h k
        rw[unfold_eq k] at hk
        rw[if_neg hkj] at hk
        rw[if_neg hki] at hk
        exact hk


lemma dot_product_smul {A : Type} [Field_ A] {n : Nat}
    (c : A) (a x : NTuple A n) :
    NTuple_dot_product (NTuple_smul c a) x = Field_.mul c (NTuple_dot_product a x) := by
  induction n with
  | zero =>
    unfold NTuple_dot_product
    unfold sum_NTuple
    rw[(MulByZeroIsZero c).left]

  | succ k ih =>
    unfold NTuple_dot_product
    unfold sum_NTuple
    unfold NTuple_smul
    have Lh : (fun i => Field_.mul (a i) (x i)) ⟨k, Nat.lt_succ_self k⟩ =
       Field_.mul (a ⟨k,Nat.lt_succ_self k⟩) (x ⟨k,Nat.lt_succ_self k⟩) := rfl
    have Lh2 : (fun i => Field_.mul (Field_.mul c (a i)) (x i)) ⟨k, Nat.lt_succ_self k⟩ =
       Field_.mul (Field_.mul c  (a ⟨k,Nat.lt_succ_self k⟩) ) (x ⟨k, Nat.lt_succ_self k⟩) := by rfl
    rw[Lh]
    rw[Lh2]
    let a' : NTuple A k := fun i => a ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩
    let x' : NTuple A k := fun i => x ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩
    have ihk := (ih a' x')
    unfold NTuple_dot_product at ihk
    unfold NTuple_smul at ihk
    have ha' : (sum_NTuple fun i => (fun i => Field_.mul (Field_.mul c (a i)) (x i)) ⟨↑i, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩) =
           (sum_NTuple fun i => Field_.mul (Field_.mul c (a' i)) (x' i)) := rfl
    rw[ha']
    rw [Field_.distribLeft c]
    rw [← Field_.mul_assoc c (a ⟨k, Nat.lt_succ_self k⟩) (x ⟨k, Nat.lt_succ_self k⟩)]
    rw [ihk]

theorem scaleRowOutputIsEquivalent {A : Type} [Field_ A] {m n : Nat}  (sys : LinearSystem A m n) (i : Fin m) (c : A) (hc : c ≠ Field_.zero): AreEquivalent sys ((scaleRow sys i) c)  := by
  unfold AreEquivalent
  intro x
  unfold IsSystemSolution scaleRow
  have unfold_eq : ∀ k : Fin m,
    (({ equations := fun k =>
        if k = i then { a := NTuple_smul c (sys.equations i).a,
                        b := Field_.mul c (sys.equations i).b }
        else sys.equations k } : LinearSystem A m n).equations k) =
    (if k = i then { a := NTuple_smul c (sys.equations i).a,
                     b := Field_.mul c (sys.equations i).b }
     else sys.equations k) := fun k => rfl
  have ha : (LinearEquation.mk (NTuple_smul c (sys.equations i).a)
                                (Field_.mul c (sys.equations i).b)).a =
            NTuple_smul c (sys.equations i).a := rfl

  have hb : (LinearEquation.mk (NTuple_smul c (sys.equations i).a)
                                (Field_.mul c (sys.equations i).b)).b =
            Field_.mul c (sys.equations i).b := rfl

  constructor
  ·
    intro h k
    unfold IsSolution
    unfold IsSolution at h
    by_cases hki : k = i
    .
      have hk := h i
      rw[unfold_eq]
      rw[if_pos hki]
      rw[ha]
      rw[hb]
      rw[←hk]
      rw[dot_product_smul]
    .
      rw[unfold_eq]
      rw[if_neg hki]
      exact h k
  · intro h k
    unfold IsSolution
    unfold IsSolution at h
    by_cases hki : k = i
    · have hk := h i
      rw [unfold_eq i, if_pos rfl] at hk
      rw [ha, hb] at hk
      rw [dot_product_smul] at hk
      rw [hki]
      have hcancel : NTuple_dot_product (sys.equations i).a x = (sys.equations i).b := by
        have h1 : Field_.mul (inv c hc) (Field_.mul c (NTuple_dot_product (sys.equations i).a x)) =
                  Field_.mul (inv c hc) (Field_.mul c (sys.equations i).b) := by
          rw [hk]
        rw [← Field_.mul_assoc, ← Field_.mul_assoc] at h1
        rw [(MulInverseCancel c hc).right] at h1
        rw [(Field_.mul_neut _).left, (Field_.mul_neut _).left] at h1
        exact h1
      exact hcancel
    · have hk := h k
      rw [unfold_eq k, if_neg hki] at hk
      exact hk

lemma dot_product_add {A : Type} [Field_ A] {n : Nat}
    (a b x : NTuple A n) :
    NTuple_dot_product (NTuple_add a b) x =
    Field_.add (NTuple_dot_product a x) (NTuple_dot_product b x) := by
  induction n with
  | zero =>
      unfold NTuple_dot_product NTuple_add sum_NTuple
      rw [(Field_.add_neut (Field_.zero : A)).left]
  | succ k ih =>
      unfold NTuple_dot_product NTuple_add sum_NTuple
      let a' : NTuple A k := fun i => a ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩
      let b' : NTuple A k := fun i => b ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩
      let x' : NTuple A k := fun i => x ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩
      have ihk := ih a' b' x'
      unfold NTuple_dot_product NTuple_add at ihk
      have hk : (fun i => Field_.mul (Field_.add (a i) (b i)) (x i)) ⟨k, Nat.lt_succ_self k⟩ =
                Field_.add (Field_.mul (a ⟨k, Nat.lt_succ_self k⟩) (x ⟨k, Nat.lt_succ_self k⟩))
                           (Field_.mul (b ⟨k, Nat.lt_succ_self k⟩) (x ⟨k, Nat.lt_succ_self k⟩)) :=
        FieldDistributiveLaw.right (x ⟨k, Nat.lt_succ_self k⟩) (a ⟨k, Nat.lt_succ_self k⟩) (b ⟨k, Nat.lt_succ_self k⟩)
      have hsum : (sum_NTuple fun (i : Fin k) =>
                    (fun i => Field_.mul (Field_.add (a i) (b i)) (x i)) ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩) =
                  Field_.add (sum_NTuple fun (i : Fin k) => Field_.mul (a' i) (x' i))
                             (sum_NTuple fun (i : Fin k) => Field_.mul (b' i) (x' i)) := by
        have heq : (fun (i : Fin k) => (fun i => Field_.mul (Field_.add (a i) (b i)) (x i))
                    ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩) =
                   (fun (i : Fin k) => Field_.mul (Field_.add (a' i) (b' i)) (x' i)) := by funext i; rfl
        rw [heq]
        exact ihk
      rw [hk, hsum]
      rw [Field_.add_assoc, Field_.add_assoc]
      congr 1
      rw [← Field_.add_assoc, ← Field_.add_assoc]
      congr 1
      exact Field_.add_comm _ _

theorem addRowOutputIsEquivalent {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) (i j : Fin m) (c : A) (hijn : i ≠ j) :
    AreEquivalent sys (addRow sys i j c) := by
  unfold AreEquivalent IsSystemSolution
  intro x
  have unfold_eq : ∀ k : Fin m,
      (({ equations := fun k =>
          if k = j then
            { a := NTuple_add (sys.equations j).a (NTuple_smul c (sys.equations i).a),
              b := Field_.add (sys.equations j).b (Field_.mul c (sys.equations i).b) }
          else sys.equations k } : LinearSystem A m n).equations k) =
      (if k = j then
            { a := NTuple_add (sys.equations j).a (NTuple_smul c (sys.equations i).a),
              b := Field_.add (sys.equations j).b (Field_.mul c (sys.equations i).b) }
          else sys.equations k) := fun k => rfl
  have ha' : (LinearEquation.mk
                (NTuple_add (sys.equations j).a (NTuple_smul c (sys.equations i).a))
                (Field_.add (sys.equations j).b (Field_.mul c (sys.equations i).b))).a =
             NTuple_add (sys.equations j).a (NTuple_smul c (sys.equations i).a) := rfl
  have hb' : (LinearEquation.mk
                (NTuple_add (sys.equations j).a (NTuple_smul c (sys.equations i).a))
                (Field_.add (sys.equations j).b (Field_.mul c (sys.equations i).b))).b =
             Field_.add (sys.equations j).b (Field_.mul c (sys.equations i).b) := rfl
  unfold addRow
  constructor
  · intro h k
    unfold IsSolution
    by_cases hkj : k = j
    · rw [hkj, unfold_eq j, if_pos rfl, ha', hb']
      have hj := h j
      have hi := h i
      unfold IsSolution at hj hi
      rw [dot_product_add, dot_product_smul, hj, hi]
    · rw [unfold_eq k, if_neg hkj]
      exact h k
  · intro h k
    unfold IsSolution
    by_cases hkj : k = j
    · have hj := h j
      have hi := h i
      unfold IsSolution at hj hi
      rw [unfold_eq j, if_pos rfl, ha', hb'] at hj
      rw [unfold_eq i, if_neg hijn] at hi
      rw [dot_product_add, dot_product_smul] at hj
      rw [hi] at hj
      rw [hkj]
      have h1 : Field_.add
                  (Field_.add (NTuple_dot_product (sys.equations j).a x) (Field_.mul c (sys.equations i).b))
                  (neg (Field_.mul c (sys.equations i).b)) =
                Field_.add
                  (Field_.add (sys.equations j).b (Field_.mul c (sys.equations i).b))
                  (neg (Field_.mul c (sys.equations i).b)) := by rw [hj]
      rw [Field_.add_assoc, Field_.add_assoc,
          (AddInverseCancel _).left,
          (Field_.add_neut _).right,
          (Field_.add_neut _).right] at h1
      exact h1
    · have hk := h k
      rw [unfold_eq k, if_neg hkj] at hk
      exact hk
