import RubikSTM.Proofs.OBTM.Compiler.GroupedCommutingProd
import Mathlib
set_option autoImplicit false

theorem RubikOBTMCompiler.grouped_commuting_prod :
    ∀ {I P G : Type*} [DecidableEq P] [Monoid G]
  (Y : Finset I) (v : I → G) (hc : ∀ i j, Commute (v i) (v j))
  (w : I → P) (A : Finset P) (hw : ∀ d∈Y, w d∈A), (A.toList.map (fun p => (((Y.filter (fun d => w d=p)).toList).map v).reverse.prod)).reverse.prod =
    (Y.toList.map v).reverse.prod :=
  @proof_RubikOBTMCompiler_grouped_commuting_prod
