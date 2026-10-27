import RubikSTM.Proofs.Solved.obtm_fixedRadius_count
import RubikSTM.Definitions.Solved.Metrics
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikSolved.obtm_fixedRadius_count :
    ∀ {n : ℕ} (hn : 2 ≤ n) (d : ℕ) (hcover : ∀ p : Rubik.Position n, RubikSolved.solvedLookingDistance (RubikOBTM.obtmGraph n) p ≤ d), Fintype.card (Rubik.Position n) ≤ 6 ^ 6 * (18 * (n - 1) + 1) ^ d :=
  @proof_RubikSolved_obtm_fixedRadius_count
