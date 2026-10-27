import RubikSTM.Proofs.Solved.solvedLooking_card_le
import RubikSTM.Definitions.Solved.Metrics
set_option autoImplicit false

theorem RubikSolved.solvedLooking_card_le :
    ∀ (n : ℕ), Nat.card {p : Rubik.Position n // RubikSolved.IsSolvedLooking p} ≤ 6 ^ 6 :=
  @proof_RubikSolved_solvedLooking_card_le
