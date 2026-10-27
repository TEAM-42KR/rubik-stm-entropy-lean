import RubikSTM.Proofs.Solved.radius_comparison
import RubikSTM.Definitions.Solved.Metrics
set_option autoImplicit false

theorem RubikSolved.radius_comparison :
    ∀ {n : ℕ} (G : SimpleGraph (Rubik.Position n)) (hc : G.Connected), RubikSolved.solvedLookingRadius G ≤ RubikSolved.solvedRadius G ∧ RubikSolved.solvedRadius G ≤ G.diam :=
  @proof_RubikSolved_radius_comparison
