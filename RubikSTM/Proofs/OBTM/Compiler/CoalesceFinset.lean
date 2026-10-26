import Mathlib
set_option autoImplicit false
open scoped IsMulCommutative

theorem proof_RubikOBTMCompiler_coalesce_finset {I P : Type*} [DecidableEq P] [CommMonoid P]
  (Y : Finset I) (w : I → P) (A : Finset P) (hw : ∀ d∈Y, w d∈A) (R : I → Prop) [DecidablePred R] :
  (∏ p∈A, p ^ ((Y.filter (fun d => w d=p)).filter R).card) =
    ∏ d∈Y.filter R, w d := by
  classical
  have H := Finset.prod_fiberwise_of_maps_to' (s:=Y.filter R) (t:=A) (g:=w)
    (fun d hd => hw d (Finset.mem_filter.mp hd).1) (fun p => p)
  simpa [Finset.filter_filter,and_comm] using H

#print axioms proof_RubikOBTMCompiler_coalesce_finset
