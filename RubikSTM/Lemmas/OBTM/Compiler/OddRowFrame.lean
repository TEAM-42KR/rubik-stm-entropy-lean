import RubikSTM.Proofs.OBTM.Compiler.OddRowFrame
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.UniversalOwnProfile
set_option autoImplicit false

theorem RubikOBTMCompiler.odd_row_frame :
    ∀ {G : Type*} [Group G] (Q F : G) (hQ : Q^2=1)
  (t j : ℕ) (hj : 1≤j) (hjt : j≤t) (ht : t%2=1), Q^(t-j)*F*Q^(j-1) = (Q^((j-1)%2))⁻¹ * F * Q^((j-1)%2) :=
  @proof_RubikOBTMCompiler_odd_row_frame
