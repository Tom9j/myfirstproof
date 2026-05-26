import LinerAlgbra.chapter1_2

-- ==========================================
-- הגדרות בסיסיות: וקטור, שוויון
-- ==========================================

def Ntuple (A : Type) (n : Nat) := Fin n → A

def Ntuple_Equal {A : Type} {n : Nat} (u v : Ntuple A n) : Prop :=
  ∀ i, u i = v i

-- ==========================================
-- חיבור וקטורים
-- ==========================================

def Ntuple_add {A : Type} [Field_ A] {n : Nat} : Operation (Ntuple A n) (Ntuple A n) (Ntuple A n) :=
  fun u v => fun i => Field_.add (u i) (v i)

theorem Ntuple_add_Is_Closed {A : Type} [Field_ A] {n : Nat}: IsClosedOp (Ntuple A n) Ntuple_add := by
  unfold IsClosedOp
  intro a b
  use (Ntuple_add a b)

theorem Ntuple_Add_Is_Assoc {A : Type} [Field_ A] {n : Nat} :
    IsAssociativeOp (Ntuple A n) Ntuple_add := by
  unfold IsAssociativeOp
  intro a b c
  funext i
  unfold Ntuple_add
  rw [Field_.add_assoc]

theorem Ntuple_Add_comm {A : Type} {n : Nat} [Field_ A] :
    IsCommutativeOp (Ntuple A n) (Ntuple_add) := by
  unfold IsCommutativeOp
  intro a b
  unfold Ntuple_add
  funext x
  rw[Field_.add_comm]

def Ntuple_zero {A : Type} [Field_ A] {n : Nat} : Ntuple A n :=
  fun _ => Field_.zero

theorem Ntuple_add_neut {A : Type} {n : Nat} [Field_ A] :
    IsNeutralElement (Ntuple A n) (Ntuple_add) (Ntuple_zero) := by
  unfold IsNeutralElement Ntuple_add Ntuple_zero
  intro a
  constructor
  · funext x
    rw[(Field_.add_neut (a x)).left]
  · funext x
    rw[(Field_.add_neut (a x)).right]

noncomputable def Ntuple_neg {A : Type} [Field_ A] {n : Nat} (v : Ntuple A n) : Ntuple A n :=
  fun i => neg (v i)

theorem Ntuple_add_HasInv {A : Type} {n : Nat} [Field_ A] :
    AllElementsHaveInverse (Ntuple A n) Ntuple_add Ntuple_zero Ntuple_add_neut := by
  unfold AllElementsHaveInverse Ntuple_add
  intro a
  unfold IsInverseElement
  use Ntuple_neg a
  unfold Ntuple_neg
  constructor
  · funext x
    have h : (fun (u : Ntuple A n) (v : Ntuple A n) (i : Fin n) => Field_.add (u i) (v i)) a (fun i => -(a i)) x = Field_.add (a x) (neg (a x)) := rfl
    rw[h]
    rw[(AddInverseCancel (a x)).left]
    rfl
  · funext x
    have h : (fun (u : Ntuple A n) (v : Ntuple A n) (i : Fin n) => Field_.add (u i) (v i)) (fun i => -(a i)) a x = Field_.add (neg (a x)) (a x) := rfl
    rw[h]
    rw[(AddInverseCancel (a x)).right]
    rfl

-- ==========================================
-- כפל בסקלר
-- ==========================================

def Ntuple_smul {A : Type} [Field_ A] {n : Nat} : Operation A (Ntuple A n) (Ntuple A n) :=
  fun c v => fun i => Field_.mul c (v i)

theorem Ntuple_smul_on_zero {A : Type} [Field_ A] {n : Nat} (v : Ntuple A n) : Ntuple_smul Field_.zero v = Ntuple_zero := by
  funext i
  unfold Ntuple_smul Ntuple_zero
  rw [(MulByZeroIsZero (v i)).right]

theorem Ntuple_smul_mulbyone {A : Type} [Field_ A] {n : Nat} (v : Ntuple A n) : Ntuple_smul Field_.one v = v := by
  unfold Ntuple_smul
  funext i
  rw[(Field_.mul_neut (v i)).left]

theorem Ntuple_smul_mulbynegone {A : Type} [Field_ A] {n : Nat} (v : Ntuple A n) : Ntuple_smul (neg (Field_.one)) v = (Ntuple_neg v) := by
  unfold Ntuple_smul Ntuple_neg
  funext i
  rw[(OneNegTimesEqNeg (v i)).left]

-- 1. חוק הקיבוציות המדויק לכפל בסקלר: (a * b) * v = a * (b * v)
theorem Ntuple_smul_assoc_true {A : Type} [Field_ A] {n : Nat} (a b : A) (v : Ntuple A n) :
  Ntuple_smul (Field_.mul a b) v = Ntuple_smul a (Ntuple_smul b v) := by
  unfold Ntuple_smul
  funext i
  rw [Field_.mul_assoc]

-- 2. חילוף סקלרים: כפל ב-a ואז ב-b שווה לכפל ב-b ואז ב-a
theorem Ntuple_smul_scalars_comm {A : Type} [Field_ A] {n : Nat} (a b : A) (v : Ntuple A n) :
  Ntuple_smul b (Ntuple_smul a v) = Ntuple_smul a (Ntuple_smul b v) := by
  unfold Ntuple_smul
  funext i
  rw [Field_.mul_comm a (v i)]
  rw [←Field_.mul_assoc b (v i) a]
  rw [Field_.mul_comm]

-- ==========================================
-- חוקי הפילוג
-- ==========================================

-- פילוג משמאל (סקלר כפול סכום וקטורים)
theorem Ntuple_smul_distrib_left {A : Type} [Field_ A] {n : Nat} (c : A) (u v : Ntuple A n) :
  Ntuple_smul c (Ntuple_add u v) = Ntuple_add (Ntuple_smul c u) (Ntuple_smul c v) := by
  unfold Ntuple_smul Ntuple_add
  funext i
  exact Field_.distribLeft c (u i) (v i)

-- פילוג מימין (סכום סקלרים כפול וקטור)
theorem Ntuple_smul_distrib_right {A : Type} [Field_ A] {n : Nat} (a b : A) (v : Ntuple A n) :
  Ntuple_smul (Field_.add a b) v = Ntuple_add (Ntuple_smul a v) (Ntuple_smul b v) := by
  unfold Ntuple_smul Ntuple_add
  funext i
  exact FieldDistributiveLaw.right (v i) a b

def sum_Ntuple {A : Type} [Field_ A] : {n : Nat} → Ntuple A n → A
  | 0, _ => Field_.zero
  | k + 1, v => Field_.add (v ⟨k, Nat.lt_succ_self k⟩)
                           (sum_Ntuple (fun i => v ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩))

def Ntuple_dot_product {A : Type} [Field_ A] {n : Nat} (a x : Ntuple A n) : A :=
  sum_Ntuple (fun i => Field_.mul (a i) (x i))

structure LinearEquation (A : Type) [Field_ A] (n : Nat) where
  a : Ntuple A n
  b : A

def IsSolution {A : Type} [Field_ A] {n : Nat}
    (eq : LinearEquation A n) (x : Ntuple A n) : Prop :=
  Ntuple_dot_product eq.a x = eq.b

structure LinearSystem (A : Type) [Field_ A] (m n : Nat) where
  equations : Ntuple (LinearEquation A n) m

def IsSystemSolution {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) (x : Ntuple A n) : Prop :=
  ∀ i : Fin m, IsSolution (sys.equations i) x

def IsHomogeneous (A : Type) [Field_ A] {m n : Nat} (v : LinearSystem A m n) :=
  ∀ i : Fin m, (v.equations i).b = Field_.zero

-- לא מהספר הוכחה שלי

theorem sum_Ntuple_zero {A : Type} [Field_ A] (n : Nat) :
    sum_Ntuple (Ntuple_zero : Ntuple A n) = Field_.zero := by
    induction n with
    | zero =>
    rfl
    | succ k ih =>
    unfold sum_Ntuple
    have h : (Ntuple_zero ⟨k, Nat.lt_succ_self k⟩ = (Field_.zero : A)) := by
      rfl
    rw[h]
    rw[(Field_.add_neut (sum_Ntuple fun i => Ntuple_zero ⟨↑i, _⟩)).left]
    exact ih

-- לא מהספר הוכחה שלי

theorem sum_Ntuple_neg {A : Type} [Field_ A] {n : Nat} (v : Ntuple A n) :
    sum_Ntuple (Ntuple_neg v) = neg (sum_Ntuple v) := by
    induction n with
    | zero =>
      unfold sum_Ntuple
      conv_lhs => rw[zeronegeqzero]

    | succ k ih =>
      unfold sum_Ntuple

      have ihv := ih ( fun (i : Fin k)=> v ⟨↑i,Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩)
      rw[SumOfNegEQNEGADDNEG]
      rw[←ihv]
      have h :  (Ntuple_neg v ⟨k, Nat.lt_succ_self k⟩) = (neg (v ⟨k, Nat.lt_succ_self k⟩)) := by
        unfold Ntuple_neg
        rfl
      rw[h]
      rfl

-- לא מהספר הוכחה שלי

theorem sum_Ntuple_add {A : Type} [Field_ A] {n : Nat} (u v : Ntuple A n) :
    sum_Ntuple (Ntuple_add u v) = Field_.add (sum_Ntuple u) (sum_Ntuple v) := by
    unfold Ntuple_add
    induction n with
    |zero =>
      unfold sum_Ntuple
      rw[(Field_.add_neut Field_.zero).left]
    | succ k ih =>
      unfold sum_Ntuple
      rw[Field_.add_comm (u ⟨k, _⟩) (sum_Ntuple fun i => u ⟨↑i, _⟩)]
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
      rw[AddCanBeFour (sum_Ntuple u') (u ⟨k, _⟩) (v ⟨k, _⟩) (sum_Ntuple v')]
      rw[Field_.add_comm]


lemma dot_product_with_zero {A : Type} [Field_ A] {n : Nat}
    (v : Ntuple A n) : Ntuple_dot_product v Ntuple_zero = Field_.zero := by
    unfold Ntuple_dot_product Ntuple_zero
    have h : (fun i => Field_.mul (v i) Field_.zero) = fun (anyIndex : Fin n) => Field_.zero := by
      funext i
      exact (MulByZeroIsZero (v i)).left
    rw [h]
    clear v h
    induction n with
    | zero =>
        unfold sum_Ntuple
        rfl
    | succ n ih =>
        unfold sum_Ntuple
        have h2 : (fun i : Fin n => (fun (bigIndex : Fin (n+1)) => (Field_.zero : A))
                  ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩) =
                  fun (anyIndex : Fin n) => (Field_.zero : A) := by
          funext i
          rfl
        rw [h2, ih]
        exact (Field_.add_neut Field_.zero).left

theorem IfxEqZeroThesEveryHomogeneouswithxHasSolution (A : Type) [Field_ A] {m n : Nat} (v : LinearSystem A m n) (h : IsHomogeneous A v) : IsSystemSolution v Ntuple_zero := by
  unfold IsSystemSolution Ntuple_zero
  unfold IsHomogeneous at h
  intro i
  unfold IsSolution
  have h1 : (v.equations i).b = Field_.zero := by exact (h i)
  rw[h1]
  exact dot_product_with_zero (v.equations i).a

def AreEquivalent {A : Type} [Field_ A] {m₁ m₂ n : Nat}
    (sys1 : LinearSystem A m₁ n)
    (sys2 : LinearSystem A m₂ n) : Prop :=
  ∀ x : Ntuple A n, IsSystemSolution sys1 x ↔ IsSystemSolution sys2 x

def swapRows {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) (i j : Fin m) : LinearSystem A m n :=
  { equations := fun k =>
      if k = i then sys.equations j
      else if k = j then sys.equations i
      else sys.equations k }

def scaleRow {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) (i : Fin m) (c : A) : LinearSystem A m n :=
  { equations := fun k =>
      if k = i then { a := Ntuple_smul c (sys.equations i).a,
                      b := Field_.mul c (sys.equations i).b }
      else sys.equations k }

def addRow {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) (i j : Fin m) (c : A) : LinearSystem A m n :=
  { equations := fun k =>
      if k = j then { a := Ntuple_add (sys.equations j).a (Ntuple_smul c (sys.equations i).a),
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

-- לא מהספר הוכחה שלי

lemma dot_product_smul {A : Type} [Field_ A] {n : Nat}
    (c : A) (a x : Ntuple A n) :
    Ntuple_dot_product (Ntuple_smul c a) x = Field_.mul c (Ntuple_dot_product a x) := by
  induction n with
  | zero =>
    unfold Ntuple_dot_product
    unfold sum_Ntuple
    rw[(MulByZeroIsZero c).left]

  | succ k ih =>
    unfold Ntuple_dot_product
    unfold sum_Ntuple
    unfold Ntuple_smul
    have Lh : (fun i => Field_.mul (a i) (x i)) ⟨k, Nat.lt_succ_self k⟩ =
       Field_.mul (a ⟨k,Nat.lt_succ_self k⟩) (x ⟨k,Nat.lt_succ_self k⟩) := rfl
    have Lh2 : (fun i => Field_.mul (Field_.mul c (a i)) (x i)) ⟨k, Nat.lt_succ_self k⟩ =
       Field_.mul (Field_.mul c  (a ⟨k,Nat.lt_succ_self k⟩) ) (x ⟨k, Nat.lt_succ_self k⟩) := by rfl
    rw[Lh]
    rw[Lh2]
    let a' : Ntuple A k := fun i => a ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩
    let x' : Ntuple A k := fun i => x ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩
    have ihk := (ih a' x')
    unfold Ntuple_dot_product at ihk
    unfold Ntuple_smul at ihk
    have ha' : (sum_Ntuple fun i => (fun i => Field_.mul (Field_.mul c (a i)) (x i)) ⟨↑i, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩) =
           (sum_Ntuple fun i => Field_.mul (Field_.mul c (a' i)) (x' i)) := rfl
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
        if k = i then { a := Ntuple_smul c (sys.equations i).a,
                        b := Field_.mul c (sys.equations i).b }
        else sys.equations k } : LinearSystem A m n).equations k) =
    (if k = i then { a := Ntuple_smul c (sys.equations i).a,
                     b := Field_.mul c (sys.equations i).b }
     else sys.equations k) := fun k => rfl
  have ha : (LinearEquation.mk (Ntuple_smul c (sys.equations i).a)
                                (Field_.mul c (sys.equations i).b)).a =
            Ntuple_smul c (sys.equations i).a := rfl

  have hb : (LinearEquation.mk (Ntuple_smul c (sys.equations i).a)
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
      have hcancel : Ntuple_dot_product (sys.equations i).a x = (sys.equations i).b := by
        have h1 : Field_.mul (inv c hc) (Field_.mul c (Ntuple_dot_product (sys.equations i).a x)) =
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

-- לא מהספר הוכחה שלי

lemma dot_product_add {A : Type} [Field_ A] {n : Nat}
    (a b x : Ntuple A n) :
    Ntuple_dot_product (Ntuple_add a b) x =
    Field_.add (Ntuple_dot_product a x) (Ntuple_dot_product b x) := by
  induction n with
  | zero =>
      unfold Ntuple_dot_product Ntuple_add sum_Ntuple
      rw [(Field_.add_neut (Field_.zero : A)).left]
  | succ k ih =>
      unfold Ntuple_dot_product Ntuple_add sum_Ntuple
      let a' : Ntuple A k := fun i => a ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩
      let b' : Ntuple A k := fun i => b ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩
      let x' : Ntuple A k := fun i => x ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩
      have ihk := ih a' b' x'
      unfold Ntuple_dot_product Ntuple_add at ihk
      have hk : (fun i => Field_.mul (Field_.add (a i) (b i)) (x i)) ⟨k, Nat.lt_succ_self k⟩ =
                Field_.add (Field_.mul (a ⟨k, Nat.lt_succ_self k⟩) (x ⟨k, Nat.lt_succ_self k⟩))
                           (Field_.mul (b ⟨k, Nat.lt_succ_self k⟩) (x ⟨k, Nat.lt_succ_self k⟩)) :=
        FieldDistributiveLaw.right (x ⟨k, Nat.lt_succ_self k⟩) (a ⟨k, Nat.lt_succ_self k⟩) (b ⟨k, Nat.lt_succ_self k⟩)
      have hsum : (sum_Ntuple fun (i : Fin k) =>
                    (fun i => Field_.mul (Field_.add (a i) (b i)) (x i)) ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩) =
                  Field_.add (sum_Ntuple fun (i : Fin k) => Field_.mul (a' i) (x' i))
                             (sum_Ntuple fun (i : Fin k) => Field_.mul (b' i) (x' i)) := by
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
            { a := Ntuple_add (sys.equations j).a (Ntuple_smul c (sys.equations i).a),
              b := Field_.add (sys.equations j).b (Field_.mul c (sys.equations i).b) }
          else sys.equations k } : LinearSystem A m n).equations k) =
      (if k = j then
            { a := Ntuple_add (sys.equations j).a (Ntuple_smul c (sys.equations i).a),
              b := Field_.add (sys.equations j).b (Field_.mul c (sys.equations i).b) }
          else sys.equations k) := fun k => rfl
  have ha' : (LinearEquation.mk
                (Ntuple_add (sys.equations j).a (Ntuple_smul c (sys.equations i).a))
                (Field_.add (sys.equations j).b (Field_.mul c (sys.equations i).b))).a =
             Ntuple_add (sys.equations j).a (Ntuple_smul c (sys.equations i).a) := rfl
  have hb' : (LinearEquation.mk
                (Ntuple_add (sys.equations j).a (Ntuple_smul c (sys.equations i).a))
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
                  (Field_.add (Ntuple_dot_product (sys.equations j).a x) (Field_.mul c (sys.equations i).b))
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
