import RubikSTM.Proofs.Solved.obtm_radius_card_le
import RubikSTM.Definitions.Solved.Metrics
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikSolved.obtm_radius_card_le :
    ∀ {n : ℕ} (hn : 2 ≤ n), Fintype.card (Rubik.Position n) ≤ (18 * n + 1) ^ (RubikSolved.solvedLookingRadius (RubikOBTM.obtmGraph n) + 6) :=
  @proof_RubikSolved_obtm_radius_card_le
