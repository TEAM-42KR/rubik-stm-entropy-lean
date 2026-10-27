import RubikSTM.Proofs.Solved.solved_looks_solved
import RubikSTM.Definitions.Solved.Metrics
set_option autoImplicit false

theorem RubikSolved.solved_looks_solved :
    ∀ (n : ℕ), RubikSolved.IsSolvedLooking (RubikSolved.solvedPosition n) :=
  @proof_RubikSolved_solved_looks_solved
