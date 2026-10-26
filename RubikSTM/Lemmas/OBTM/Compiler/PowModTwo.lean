import RubikSTM.Proofs.OBTM.Compiler.PowModTwo
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.UniversalOwnProfile
set_option autoImplicit false

theorem RubikOBTMCompiler.pow_mod_two :
    ∀ {G : Type*} [Group G] (Q : G) (hQ : Q^2=1) (m : ℕ), Q^m = Q^(m%2) :=
  @proof_RubikOBTMCompiler_pow_mod_two
