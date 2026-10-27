import RubikSTM.Definitions.Solved.Metrics
set_option autoImplicit false

theorem proof_RubikSolved_solved_looks_solved (n : ℕ) : RubikSolved.IsSolvedLooking (RubikSolved.solvedPosition n) := by
  exact ⟨id, fun _ => rfl⟩
