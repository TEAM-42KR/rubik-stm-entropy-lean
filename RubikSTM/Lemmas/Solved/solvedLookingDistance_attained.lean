import RubikSTM.Proofs.Solved.solvedLookingDistance_attained
import RubikSTM.Definitions.Solved.Metrics
set_option autoImplicit false

theorem RubikSolved.solvedLookingDistance_attained :
    ∀ {n : ℕ} (G : SimpleGraph (Rubik.Position n)) (p : Rubik.Position n), ∃ q : Rubik.Position n, RubikSolved.IsSolvedLooking q ∧ G.dist p q = RubikSolved.solvedLookingDistance G p :=
  @proof_RubikSolved_solvedLookingDistance_attained
