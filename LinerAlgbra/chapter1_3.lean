import LinerAlgbra.chapter1_2

-- Chapter 1.3: n-tuples and operations

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
