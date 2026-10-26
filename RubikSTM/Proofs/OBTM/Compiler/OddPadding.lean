import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.UniversalOwnProfile
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_odd_padding (r : ℕ) : RubikOBTMCompiler.oddPad r ≤ 1 ∧ (r+RubikOBTMCompiler.oddPad r)%2=1 := by
  unfold RubikOBTMCompiler.oddPad
  omega

#print axioms proof_RubikOBTMCompiler_odd_padding
