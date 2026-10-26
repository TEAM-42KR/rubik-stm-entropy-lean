import Mathlib
set_option autoImplicit false

theorem proof_RubikRectangle_oneActiveBlock {G : Type*} [Group G] {t : ℕ} (B F : G) (j : Fin t) :
    (List.ofFn (fun q : Fin t => if q = j then F else B)).reverse.prod =
      B ^ (t - 1 - j.val) * F * B ^ j.val := by
  induction t with
  | zero => exact Fin.elim0 j
  | succ t ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [List.ofFn_succ, List.ofFn_const, List.prod_replicate]
    · have hz : (0 : Fin (t + 1)) ≠ j.succ := by
        intro he
        have hv := congrArg Fin.val he
        simp only [Fin.val_zero, Fin.val_succ] at hv
        omega
      simp only [List.ofFn_succ, hz, if_false, List.reverse_cons,
        List.prod_append, List.prod_singleton, Fin.succ_inj]
      rw [ih j]
      simp only [Fin.val_succ]
      have he : t + 1 - 1 - (j.val + 1) = t - 1 - j.val := by omega
      rw [he, pow_succ]
      group

#print axioms proof_RubikRectangle_oneActiveBlock
