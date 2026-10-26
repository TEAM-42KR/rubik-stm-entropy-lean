import Mathlib
set_option autoImplicit false

theorem proof_RubikCompiler_sameFrameTelescopes {G : Type*} [Group G] (a : G) (Fs : List G) :
  (Fs.map (fun F => a⁻¹ * F * a)).reverse.prod =
    a⁻¹ * Fs.reverse.prod * a := by
  induction Fs with
  | nil => simp
  | cons f fs ih =>
    simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton]
    rw [ih]
    group

#print axioms proof_RubikCompiler_sameFrameTelescopes
