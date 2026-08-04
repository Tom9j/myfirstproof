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

def makeHomogeneousSystem {A : Type} [Field_ A] (m n : Nat)
    (coefficients : Ntuple (Ntuple A n) m) : LinearSystem A m n :=
  { equations := fun i =>
      { a := coefficients i
        b := Field_.zero } }

def IsSystemSolution {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n)
    (x : Ntuple A n) : Prop :=
  ∀ i : Fin m, IsSolution (sys.equations i) x


def AreEquivalent {A : Type} [Field_ A] {m₁ m₂ n : Nat}
    (One : LinearSystem A m₁ n)
    (Two : LinearSystem A m₂ n) : Prop :=
  ∀ x : Ntuple A n,
    IsSystemSolution One x ↔ IsSystemSolution Two x


def switch {A : Type} [Field_ A] (m n : Nat)
    (sys : LinearSystem A m n) (t1 t2 : Fin m) :
    LinearSystem A m n :=
  { equations := fun k =>
      if k = t1 then sys.equations t2
      else if k = t2 then sys.equations t1
      else sys.equations k }


def replaceRow {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n)
    (i : Fin m)
    (newEq : LinearEquation A n) :
    LinearSystem A m n :=
  { equations := fun k =>
      if k = i then newEq
      else sys.equations k}

def scaleRow {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n)
    (i : Fin m)
    (c : A) :
    LinearSystem A m n :=
  { equations := fun k =>
      if k = i then
       { a := Ntuple_smul c (sys.equations i).a,
          b := Field_.mul c (sys.equations i).b }
      else
        sys.equations k }

def addRow {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n)
    (i j : Fin m)
    (c : A) :
    LinearSystem A m n :=
  { equations := fun k =>
      if k = i then
        { a := Ntuple_add (sys.equations i).a
              (Ntuple_smul c (sys.equations j).a),
          -- אפשר להחליף את הביטוי הקודם ב:
          -- ((scaleRow sys j c).equations j).a

          b := Field_.add (sys.equations i).b
              (Field_.mul c (sys.equations j).b)
          -- אפשר להחליף את הביטוי הקודם ב:
          -- ((scaleRow sys j c).equations j).b
        }
      else
        sys.equations k }

theorem SwitchIsEquivalent {A : Type} [Field_ A] (m n : Nat)
    (sys : LinearSystem A m n) (t1 t2 : Fin m) :
    AreEquivalent sys (switch m n sys t1 t2) := by
  have switch_eq (k : Fin m) :
      (switch m n sys t1 t2).equations k =
        if k = t1 then sys.equations t2
        else if k = t2 then sys.equations t1
        else sys.equations k := by
    rfl
  unfold AreEquivalent
  intro x
  constructor
  · intro h
    unfold IsSystemSolution IsSolution at h ⊢
    intro k
    rw [switch_eq k]
    by_cases hk1 : k = t1
    · rw [hk1, if_pos rfl]
      exact h t2
    · by_cases hk2 : k = t2
      · rw [hk2] at hk1 ⊢
        rw [if_neg hk1, if_pos rfl]
        exact h t1
      · rw [if_neg hk1, if_neg hk2]
        exact h k
  · intro h
    unfold IsSystemSolution IsSolution at h ⊢
    intro k
    by_cases hk1 : k = t1
    · rw [hk1]
      by_cases h21 : t2 = t1
      · have ht := h t2
        rw [switch_eq t2, if_pos h21, h21] at ht
        exact ht
      · have ht := h t2
        rw [switch_eq t2, if_neg h21, if_pos rfl] at ht
        exact ht
    · by_cases hk2 : k = t2
      · rw [hk2] at hk1 ⊢
        have ht := h t1
        rw [switch_eq t1, if_pos rfl] at ht
        exact ht
      · have hk := h k
        rw [switch_eq k, if_neg hk1, if_neg hk2] at hk
        exact hk

lemma dot_product_smul {A : Type} [Field_ A] {n : Nat}
    (c : A) (a x : Ntuple A n) :
    Ntuple_dot_product (Ntuple_smul c a) x =
      Field_.mul c (Ntuple_dot_product a x) := by
  induction n with
  | zero =>
      unfold Ntuple_dot_product
      unfold sum_Ntuple
      rw [(MulByZeroIsZero c).left]

  | succ k ih =>
      unfold Ntuple_dot_product
      unfold sum_Ntuple
      unfold Ntuple_smul
      have h1 :
          (fun i => Field_.mul (a i) (x i))
              ⟨k, Nat.lt_succ_self k⟩ =
            Field_.mul (a ⟨k, Nat.lt_succ_self k⟩)
              (x ⟨k, Nat.lt_succ_self k⟩) := by
        rfl
      have h2 :
          (fun i => Field_.mul (Field_.mul c (a i)) (x i))
              ⟨k, Nat.lt_succ_self k⟩ =
            Field_.mul (Field_.mul c (a ⟨k, Nat.lt_succ_self k⟩))
              (x ⟨k, Nat.lt_succ_self k⟩) := by
        rfl
      rw [h1, h2]
      let a' : Ntuple A k :=
        fun i => a ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩
      let x' : Ntuple A k :=
        fun i => x ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩
      have ihk := ih a' x'
      unfold Ntuple_dot_product at ihk
      unfold Ntuple_smul at ihk
      have h3 :
          (sum_Ntuple (fun i =>
            (fun i => Field_.mul (Field_.mul c (a i)) (x i))
              ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩)) =
          sum_Ntuple (fun i => Field_.mul (Field_.mul c (a' i)) (x' i)) := by
        rfl
      rw [h3]
      rw [Field_.distribLeft c]
      rw [← Field_.mul_assoc c (a ⟨k, Nat.lt_succ_self k⟩)
        (x ⟨k, Nat.lt_succ_self k⟩)]
      rw [ihk]




theorem ScaleRowIsEquivalent {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n)
    (i : Fin m)
    (c : A)
    (hc : c ≠ Field_.zero) :
    AreEquivalent sys (scaleRow sys i c) := by

  have scale_eq (k : Fin m) :
      (scaleRow sys i c).equations k =
        if k = i then
          { a := Ntuple_smul c (sys.equations i).a,
            b := Field_.mul c (sys.equations i).b }
        else
          sys.equations k := by
    rfl

  unfold AreEquivalent
  intro x
  constructor

  · intro h
    unfold IsSystemSolution IsSolution at h ⊢
    intro k
    rw [scale_eq k]

    by_cases hki : k = i
    · rw [hki, if_pos rfl]
      have h1 :
          (({ a := Ntuple_smul c (sys.equations i).a,
              b := Field_.mul c (sys.equations i).b } : LinearEquation A n).a)
            = Ntuple_smul c (sys.equations i).a := by
        rfl
      have h2 :
          (({ a := Ntuple_smul c (sys.equations i).a,
              b := Field_.mul c (sys.equations i).b } : LinearEquation A n).b)
            = Field_.mul c (sys.equations i).b := by
        rfl
      rw[h1]
      rw[h2]
      rw[dot_product_smul]
      rw[h i]

    · rw [if_neg hki]
      exact h k

  · intro h
    unfold IsSystemSolution IsSolution at h ⊢
    intro k

    by_cases hki : k = i
    · rw [hki]
      have hk := h i
      rw [scale_eq i] at hk
      rw [if_pos rfl] at hk

      change
        Ntuple_dot_product
            (Ntuple_smul c (sys.equations i).a) x =
          Field_.mul c (sys.equations i).b at hk

      rw [dot_product_smul] at hk
      have hvaa : Field_.mul (inv c hc) (Field_.mul c (Ntuple_dot_product (sys.equations i).a x)) =  (sys.equations i).b := by
          rw[hk]
          rw[←Field_.mul_assoc]
          rw[(MulInverseCancel c hc).right]
          rw[(Field_.mul_neut (sys.equations i).b).left]
      rw[←hvaa]
      rw[←Field_.mul_assoc]
      rw[(MulInverseCancel c hc).right]
      rw[(Field_.mul_neut (Ntuple_dot_product (sys.equations i).a x)).left]


    · have hk := h k
      rw [scale_eq k, if_neg hki] at hk
      exact hk


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
      let a' : Ntuple A k :=
        fun i => a ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩
      let b' : Ntuple A k :=
        fun i => b ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩
      let x' : Ntuple A k :=
        fun i => x ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩
      have ihk := ih a' b' x'
      unfold Ntuple_dot_product Ntuple_add at ihk
      have hk :
          (fun i => Field_.mul (Field_.add (a i) (b i)) (x i))
              ⟨k, Nat.lt_succ_self k⟩ =
            Field_.add
              (Field_.mul (a ⟨k, Nat.lt_succ_self k⟩)
                (x ⟨k, Nat.lt_succ_self k⟩))
              (Field_.mul (b ⟨k, Nat.lt_succ_self k⟩)
                (x ⟨k, Nat.lt_succ_self k⟩)) :=
        FieldDistributiveLaw.right (x ⟨k, Nat.lt_succ_self k⟩)
          (a ⟨k, Nat.lt_succ_self k⟩) (b ⟨k, Nat.lt_succ_self k⟩)
      have hsum :
          (sum_Ntuple (fun i =>
            (fun i => Field_.mul (Field_.add (a i) (b i)) (x i))
              ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩)) =
          Field_.add
            (sum_Ntuple (fun i => Field_.mul (a' i) (x' i)))
            (sum_Ntuple (fun i => Field_.mul (b' i) (x' i))) := by
        have heq :
            (fun i : Fin k =>
              (fun i => Field_.mul (Field_.add (a i) (b i)) (x i))
                ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩) =
            (fun i : Fin k =>
              Field_.mul (Field_.add (a' i) (b' i)) (x' i)) := by
          funext i
          rfl
        rw [heq]
        exact ihk
      rw [hk, hsum]
      rw [Field_.add_assoc, Field_.add_assoc]
      congr 1
      rw [← Field_.add_assoc, ← Field_.add_assoc]
      congr 1
      exact Field_.add_comm _ _

theorem AddRowIsEquivalent {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) (i j : Fin m) (c : A) (hij : i ≠ j) :
    AreEquivalent sys (addRow sys i j c) := by
  have add_eq (k : Fin m) :
      (addRow sys i j c).equations k =
        if k = i then
          { a := Ntuple_add (sys.equations i).a
              (Ntuple_smul c (sys.equations j).a),
            b := Field_.add (sys.equations i).b
              (Field_.mul c (sys.equations j).b) }
        else
          sys.equations k := by
    rfl
  have hji : j ≠ i := by
    intro hEq
    exact hij hEq.symm
  unfold AreEquivalent
  intro x
  constructor
  · intro h
    unfold IsSystemSolution IsSolution at h ⊢
    intro k
    rw [add_eq k]
    by_cases hki : k = i
    · rw [hki, if_pos rfl]
      change
        Ntuple_dot_product
            (Ntuple_add (sys.equations i).a
              (Ntuple_smul c (sys.equations j).a)) x =
          Field_.add (sys.equations i).b
            (Field_.mul c (sys.equations j).b)
      rw [dot_product_add, dot_product_smul, h i, h j]
    · rw [if_neg hki]
      exact h k
  · intro h
    unfold IsSystemSolution IsSolution at h ⊢
    intro k
    by_cases hki : k = i
    · rw [hki]
      have hk := h i
      rw [add_eq i, if_pos rfl] at hk
      change
        Ntuple_dot_product
            (Ntuple_add (sys.equations i).a
              (Ntuple_smul c (sys.equations j).a)) x =
          Field_.add (sys.equations i).b
            (Field_.mul c (sys.equations j).b) at hk
      rw [dot_product_add, dot_product_smul] at hk
      have hj := h j
      rw [add_eq j, if_neg hji] at hj
      rw [hj] at hk
      have hcancel :
          Field_.add
              (Ntuple_dot_product (sys.equations i).a x)
              (Field_.mul c (sys.equations j).b) =
            Field_.add (sys.equations i).b
              (Field_.mul c (sys.equations j).b) := by
        exact hk
      have hcancel' :
          Field_.add
              (Field_.add
                (Ntuple_dot_product (sys.equations i).a x)
                (Field_.mul c (sys.equations j).b))
              (neg (Field_.mul c (sys.equations j).b)) =
            Field_.add
              (Field_.add (sys.equations i).b
                (Field_.mul c (sys.equations j).b))
              (neg (Field_.mul c (sys.equations j).b)) := by
        rw [hcancel]
      rw [Field_.add_assoc, Field_.add_assoc,
          (AddInverseCancel _).left,
          (Field_.add_neut _).right,
          (Field_.add_neut _).right] at hcancel'
      exact hcancel'
    · have hk := h k
      rw [add_eq k, if_neg hki] at hk
      exact hk


inductive ElementaryOperation (A : Type) [Field_ A] (m n : Nat) where
  | switchRows (i j : Fin m)
  | scaleRow (i : Fin m) (c : A) (hc : c ≠ Field_.zero)
  | addRow (i j : Fin m) (c : A) (hij : i ≠ j)

def applyElementaryOperation {A : Type} [Field_ A] {m n : Nat} :
    ElementaryOperation A m n → LinearSystem A m n → LinearSystem A m n
  | .switchRows i j, sys => switch m n sys i j
  | .scaleRow i c _, sys => scaleRow sys i c
  | .addRow i j c _, sys => addRow sys i j c

theorem AreEquivalent_refl {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) : AreEquivalent sys sys := by
  unfold AreEquivalent
  intro x
  constructor
  · intro h
    exact h
  · intro h
    exact h

theorem AreEquivalent_trans {A : Type} [Field_ A]
    {m1 m2 m3 n : Nat}
    (sys1 : LinearSystem A m1 n)
    (sys2 : LinearSystem A m2 n)
    (sys3 : LinearSystem A m3 n)
    (h12 : AreEquivalent sys1 sys2)
    (h23 : AreEquivalent sys2 sys3) :
    AreEquivalent sys1 sys3 := by
  unfold AreEquivalent at h12 h23 ⊢
  intro x
  constructor
  · intro h
    have h2 := (h12 x).mp h
    exact (h23 x).mp h2
  · intro h
    have h2 := (h23 x).mpr h
    exact (h12 x).mpr h2

theorem elementaryOperation_equivalent {A : Type} [Field_ A]
    {m n : Nat}
    (op : ElementaryOperation A m n)
    (sys : LinearSystem A m n) :
    AreEquivalent sys (applyElementaryOperation op sys) := by
  cases op with
  | switchRows i j =>
      exact SwitchIsEquivalent m n sys i j
  | scaleRow i c hc =>
      exact ScaleRowIsEquivalent sys i c hc
  | addRow i j c hij =>
      exact AddRowIsEquivalent sys i j c hij

def applySequence {A : Type} [Field_ A] {m n : Nat} :
    (r : Nat) →
    Ntuple (ElementaryOperation A m n) r →
    LinearSystem A m n →
    LinearSystem A m n
  | 0, _, sys => sys
  | k + 1, ops, sys =>
      applyElementaryOperation (ops ⟨k, Nat.lt_succ_self k⟩)
        (applySequence k
          (fun i => ops ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩)
          sys)

theorem FiniteElementaryOperationsEquivalent
    {A : Type} [Field_ A] {m n : Nat}
    (sys : LinearSystem A m n) (r : Nat) :
    ∀ ops : Ntuple (ElementaryOperation A m n) r,
      AreEquivalent sys (applySequence r ops sys) := by
  induction r with
  | zero =>
      intro ops
      unfold applySequence
      exact AreEquivalent_refl sys
  | succ k ih =>
      intro ops
      have hprefix :
          AreEquivalent sys
            (applySequence k
              (fun i => ops ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩)
              sys) :=
        ih (fun i => ops ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩)
      have hlast := elementaryOperation_equivalent
        (ops ⟨k, Nat.lt_succ_self k⟩)
        (applySequence k
          (fun i => ops ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩)
          sys)
      change AreEquivalent sys
        (applyElementaryOperation (ops ⟨k, Nat.lt_succ_self k⟩)
          (applySequence k
            (fun i => ops ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩)
            sys))
      exact AreEquivalent_trans _ _ _ hprefix hlast
