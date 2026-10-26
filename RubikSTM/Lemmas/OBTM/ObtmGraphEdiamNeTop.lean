import RubikSTM.Proofs.OBTM.ObtmGraphEdiamNeTop
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikOBTM.obtmGraph_ediam_ne_top :
    ∀ {n : ℕ} (hn : 2 ≤ n), (RubikOBTM.obtmGraph n).ediam ≠ ⊤ :=
  @proof_RubikOBTM_obtmGraph_ediam_ne_top
