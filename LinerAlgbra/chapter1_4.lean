import LinerAlgbra.chapter1_3

-- Chapter 1.4: linear equations

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
