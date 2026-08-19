import LinerAlgbra.chapter1_6

-- Chapter 1.7: equivalent linear systems

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

def applyElementaryOperation {A : Type} [Field_ A] {m n : Nat}
    (operation : ElementaryOperation A m n)
    (currentSystem : LinearSystem A m n) :
    LinearSystem A m n :=
  match operation with
  | .switchRows row1 row2 =>
      switch m n currentSystem row1 row2
  | .scaleRow row scalar _hc =>
      scaleRow currentSystem row scalar
  | .addRow targetRow sourceRow scalar _hij =>
      addRow currentSystem targetRow sourceRow scalar
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

def applySequence {A : Type} [Field_ A] {m n : Nat}
    (length : Nat)
    (operations : Ntuple (ElementaryOperation A m n) length)
    (initialSystem : LinearSystem A m n) :
    LinearSystem A m n :=
  match length with
  | 0 =>
      initialSystem
  | k + 1 =>
      let previousOperations : Ntuple (ElementaryOperation A m n) k :=
        fun index =>
          operations ⟨index.val,
            Nat.lt_trans index.isLt (Nat.lt_succ_self k)⟩
      let systemAfterPreviousOperations : LinearSystem A m n :=
        applySequence k previousOperations initialSystem
      let lastOperation : ElementaryOperation A m n :=
        operations ⟨k, Nat.lt_succ_self k⟩
      applyElementaryOperation lastOperation systemAfterPreviousOperations



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
