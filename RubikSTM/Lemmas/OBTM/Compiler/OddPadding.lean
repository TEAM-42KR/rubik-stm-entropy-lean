import RubikSTM.Proofs.OBTM.Compiler.OddPadding
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.UniversalOwnProfile
set_option autoImplicit false

theorem RubikOBTMCompiler.odd_padding :
    ∀ (r : ℕ), RubikOBTMCompiler.oddPad r ≤ 1 ∧ (r+RubikOBTMCompiler.oddPad r)%2=1 :=
  @proof_RubikOBTMCompiler_odd_padding
