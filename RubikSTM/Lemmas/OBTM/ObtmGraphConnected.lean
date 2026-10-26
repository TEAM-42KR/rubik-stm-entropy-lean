import RubikSTM.Proofs.OBTM.ObtmGraphConnected
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikOBTM.obtmGraph_connected :
    ∀ {n : ℕ} (hn : 2 ≤ n), (RubikOBTM.obtmGraph n).Connected :=
  @proof_RubikOBTM_obtmGraph_connected
