import RubikSTM.Proofs.OBTM.Compiler.CommonFrameProgram
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.UniversalOwnProfile
set_option autoImplicit false

theorem RubikOBTMCompiler.common_frame_program :
    ∀ {G X : Type*} [Group G] [MulAction G X]
  (Q : G) (hQ : Q^2=1) (t j : ℕ) (hj : 1≤j) (hjt : j≤t) (ht : t%2=1)
  (Fs : List G) (x y : X)
  (hraw : Fs.reverse.prod • (Q^((j-1)%2) • x) = Q^((j-1)%2) • y), (Fs.map (fun F => Q^(t-j)*F*Q^(j-1))).reverse.prod =
    (Q^((j-1)%2))⁻¹ * Fs.reverse.prod * Q^((j-1)%2) ∧
  (Fs.map (fun F => Q^(t-j)*F*Q^(j-1))).reverse.prod • x = y :=
  @proof_RubikOBTMCompiler_common_frame_program
