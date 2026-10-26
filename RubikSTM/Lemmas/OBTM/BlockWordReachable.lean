import RubikSTM.Proofs.OBTM.BlockWordReachable
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikOBTM.blockWord_reachable :
    ∀ {n : ℕ} (w : List (RubikOBTM.BlockMove n)) (c : Rubik.Colouring n) (hc : Rubik.Reachable c), Rubik.Reachable (RubikOBTM.applyBlockWord w c) :=
  @proof_RubikOBTM_blockWord_reachable
