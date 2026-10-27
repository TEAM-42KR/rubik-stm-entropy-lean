import RubikSTM.Definitions.Solved.Metrics
import RubikSTM.Lemmas.Solved.solved_looks_solved
set_option autoImplicit false

theorem proof_RubikSolved_solvedLookingDistance_attained {n : ℕ} (G : SimpleGraph (Rubik.Position n))
    (p : Rubik.Position n) :
    ∃ q : Rubik.Position n, RubikSolved.IsSolvedLooking q ∧
      G.dist p q = RubikSolved.solvedLookingDistance G p := by
  have hn : {d : ℕ | ∃ q : Rubik.Position n,
      RubikSolved.IsSolvedLooking q ∧ G.dist p q = d}.Nonempty :=
    ⟨G.dist p (RubikSolved.solvedPosition n), RubikSolved.solvedPosition n,
      RubikSolved.solved_looks_solved n, rfl⟩
  exact Nat.sInf_mem hn
