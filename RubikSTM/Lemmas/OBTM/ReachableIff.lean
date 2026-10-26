import RubikSTM.Proofs.OBTM.ReachableIff
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikOBTM.reachable_iff :
    ∀ {n : ℕ} (hn : 2 ≤ n) (c : Rubik.Colouring n), RubikOBTM.BlockReachable c ↔ Rubik.Reachable c :=
  @proof_RubikOBTM_reachable_iff
