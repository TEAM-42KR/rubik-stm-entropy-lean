import RubikSTM.Proofs.OBTM.Global.UpperTail
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikOBTM.Global.upperTail :
    ∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ n : ℕ in Filter.atTop, RubikOBTM.normalizedDiameter n ≤ Rubik.entropyConstant + ε :=
  @proof_RubikOBTM_Global_upperTail
