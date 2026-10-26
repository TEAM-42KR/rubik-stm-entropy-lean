import Mathlib
set_option autoImplicit false

theorem proof_RubikCompiler_wordColouring {M X C : Type*} (move : M → Equiv.Perm X)
  (w : List M) (c : X → C) :
  w.foldl (fun state m => fun x => state ((move m)⁻¹ x)) c =
    fun x => c (((w.map move).reverse.prod)⁻¹ x) := by
  induction w generalizing c with
  | nil => rfl
  | cons m w ih =>
    simpa only [List.foldl_cons, List.map_cons, List.reverse_cons,
      List.prod_append, List.prod_singleton, mul_inv_rev, Equiv.Perm.mul_apply] using
      ih (fun x => c ((move m)⁻¹ x))

#print axioms proof_RubikCompiler_wordColouring
