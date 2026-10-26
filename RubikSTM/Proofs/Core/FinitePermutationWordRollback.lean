import Mathlib
set_option autoImplicit false

theorem proof_RubikCore_finite_permutation_word_rollback {M X : Type*} [Fintype X] (p : M → Equiv.Perm X)
    (w : List M) (x : X) :
    ∃ v : List M, v.foldl (fun z m => p m z) (w.foldl (fun z m => p m z) x) = x := by
  classical
  have hrep (m : M) (k : ℕ) (z : X) :
      (List.replicate k m).foldl (fun z m => p m z) z = (p m ^ k) z := by
    induction k generalizing z with
    | zero => rfl
    | succ k ih =>
      rw [List.replicate_succ, List.foldl_cons, ih, pow_succ, Equiv.Perm.mul_apply]
  have hone (m : M) (z : X) : ∃ v : List M, v.foldl (fun z m => p m z) (p m z) = z := by
    refine ⟨List.replicate (orderOf (p m) - 1) m, ?_⟩
    rw [hrep]
    change ((p m ^ (orderOf (p m) - 1)) * p m) z = z
    rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos (p m)), pow_orderOf_eq_one]
    rfl
  induction w generalizing x with
  | nil => exact ⟨[], rfl⟩
  | cons m w ih =>
    obtain ⟨v, hv⟩ := ih (p m x)
    obtain ⟨u, hu⟩ := hone m x
    refine ⟨v ++ u, ?_⟩
    rw [List.foldl_append, List.foldl_cons, hv, hu]

#print axioms proof_RubikCore_finite_permutation_word_rollback
