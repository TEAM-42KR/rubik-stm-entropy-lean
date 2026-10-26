import RubikSTM.Proofs.OBTM.Global.CleanupScalarBound
import Mathlib
set_option autoImplicit false

theorem RubikOBTM.Global.cleanup_scalar_bound :
    ∀ (C core m cnt n : ℕ) (hm : m ≤ n) (hn : 1 ≤ n), ((C * (cnt + 6 * m) + 4 * core : ℕ) : ℝ) ≤ (C : ℝ) * cnt + (6 * (C : ℝ) + 4 * (core : ℝ)) * n :=
  @proof_RubikOBTM_Global_cleanup_scalar_bound
