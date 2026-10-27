import RubikSTM.Proofs.Solved.solvedLookingDistance_le
import RubikSTM.Definitions.Solved.Metrics
set_option autoImplicit false

theorem RubikSolved.solvedLookingDistance_le :
    ∀ {n : ℕ} (G : SimpleGraph (Rubik.Position n)) (p q : Rubik.Position n) (hq : RubikSolved.IsSolvedLooking q), RubikSolved.solvedLookingDistance G p ≤ G.dist p q :=
  @proof_RubikSolved_solvedLookingDistance_le
