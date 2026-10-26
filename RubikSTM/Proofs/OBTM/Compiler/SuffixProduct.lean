import Mathlib
set_option autoImplicit false
open scoped IsMulCommutative

theorem proof_RubikOBTMCompiler_suffix_product {s : ℕ} {K : Type*} [CommMonoid K]
  (w : Fin s → K) (b : ℕ) : ((List.ofFn w).drop b).prod =
    ∏ d ∈ (Finset.univ.filter (fun d : Fin s => b ≤ d.val)), w d := by
  induction s generalizing b with
  | zero => simp
  | succ s ih =>
    cases b with
    | zero => simp [List.prod_ofFn,Fin.prod_univ_succ]
    | succ b =>
      simp only [List.ofFn_succ,List.drop_succ_cons]
      rw [ih]
      simp [Finset.prod_filter,Fin.prod_univ_succ]

#print axioms proof_RubikOBTMCompiler_suffix_product
