import RubikSTM.Proofs.OBTM.Compiler.LowerHalfCoalesces
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.UniversalOwnProfile
set_option autoImplicit false

theorem RubikOBTMCompiler.lower_half_coalesces :
    ∀ {G : Type*} [Group G] (D : G) (hD : D^4=1) (m : ℕ), (D^2)⁻¹ ^ m = D ^ (2*(m%2)) :=
  @proof_RubikOBTMCompiler_lower_half_coalesces
