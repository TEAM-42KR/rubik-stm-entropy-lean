import RubikSTM.Proofs.WordConstruction.PadCount
import Mathlib
set_option autoImplicit false

theorem RubikCompiler.padCount :
    ∀ (r : ℕ), (5 - r % 4) % 4 ≤ 3 ∧ (r + (5 - r % 4) % 4) % 4 = 1 :=
  @proof_RubikCompiler_padCount
