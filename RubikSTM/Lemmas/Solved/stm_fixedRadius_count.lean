import RubikSTM.Proofs.Solved.stm_fixedRadius_count
import RubikSTM.Definitions.Solved.Metrics
set_option autoImplicit false

theorem RubikSolved.stm_fixedRadius_count :
    ∀ (n d : ℕ) (hcover : ∀ p : Rubik.Position n, RubikSolved.solvedLookingDistance (Rubik.stmGraph n) p ≤ d), Fintype.card (Rubik.Position n) ≤ 6 ^ 6 * (9 * n + 1) ^ d :=
  @proof_RubikSolved_stm_fixedRadius_count
