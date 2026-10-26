import RubikSTM.Proofs.OBTM.BlockReachable
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikOBTM.block_reachable :
    ∀ {n : ℕ} (m : RubikOBTM.BlockMove n) (c : Rubik.Colouring n) (hc : Rubik.Reachable c), Rubik.Reachable (RubikOBTM.applyBlock m c) :=
  @proof_RubikOBTM_block_reachable
