import RubikSTM.Proofs.OBTM.Global.LowerTail
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikOBTM.Global.lowerTail :
    ∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ n : ℕ in Filter.atTop, Rubik.entropyConstant - ε ≤ RubikOBTM.normalizedDiameter n :=
  @proof_RubikOBTM_Global_lowerTail
