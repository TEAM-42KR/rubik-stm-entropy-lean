import RubikSTM.Proofs.Solved.stm_radius_card_le
import RubikSTM.Definitions.Solved.Metrics
set_option autoImplicit false

theorem RubikSolved.stm_radius_card_le :
    ∀ {n : ℕ} (hn : 2 ≤ n), Fintype.card (Rubik.Position n) ≤ (9 * n + 1) ^ (RubikSolved.solvedLookingRadius (Rubik.stmGraph n) + 6) :=
  @proof_RubikSolved_stm_radius_card_le
