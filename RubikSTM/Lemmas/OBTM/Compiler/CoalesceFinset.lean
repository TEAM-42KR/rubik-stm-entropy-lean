import RubikSTM.Proofs.OBTM.Compiler.CoalesceFinset
import Mathlib
set_option autoImplicit false

theorem RubikOBTMCompiler.coalesce_finset :
    ∀ {I P : Type*} [DecidableEq P] [CommMonoid P]
  (Y : Finset I) (w : I → P) (A : Finset P) (hw : ∀ d∈Y, w d∈A) (R : I → Prop) [DecidablePred R], (∏ p∈A, p ^ ((Y.filter (fun d => w d=p)).filter R).card) =
    ∏ d∈Y.filter R, w d :=
  @proof_RubikOBTMCompiler_coalesce_finset
