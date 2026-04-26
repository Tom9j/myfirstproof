import LinerAlgbra.chapter1_1

theorem ForEveryElementInFieldExistOnlyOneInvertNumber_test {A : Type} [Field_ A] (a : A) : 
  ∃! b : A, Field_.add a b = Field_.zero := by
    obtain ⟨b, hb⟩ := Field_.add_inv a
    apply ExistsUnique.intro b  
    · exact hb.left
    · intro y h
      -- Goal is y = b
      -- We have:
      -- hb.left : add a b = zero
      -- hb.right : add b a = zero
      -- h : add a y = zero
      -- We need to prove y = b
      -- y = add zero y  (from add_neut)
      --   = add (add b a) y (from hb.right)
      --   = add b (add a y) (from add_assoc)
      --   = add b zero      (from h)
      --   = b               (from add_neut)
      
      have h1 : y = Field_.add Field_.zero y := by
        have neut := Field_.add_neut y
        exact neut.left.symm
        
      have h2 : Field_.add Field_.zero y = Field_.add (Field_.add b a) y := by
        rw [hb.right]
        
      have h3 : Field_.add (Field_.add b a) y = Field_.add b (Field_.add a y) := by
        exact Field_.add_assoc b a y
        
      have h4 : Field_.add b (Field_.add a y) = Field_.add b Field_.zero := by
        rw [h]
        
      have h5 : Field_.add b Field_.zero = b := by
        have neut := Field_.add_neut b
        exact neut.right
        
      rw [h1, h2, h3, h4, h5]
