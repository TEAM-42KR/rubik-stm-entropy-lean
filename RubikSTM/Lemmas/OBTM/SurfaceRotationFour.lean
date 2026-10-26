import RubikSTM.Proofs.OBTM.SurfaceRotationFour
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikOBTM.surfaceRotation_four :
    ∀ (n : ℕ) (a : Rubik.Axis), Rubik.surfaceRotation n a ^ 4 = 1 :=
  @proof_RubikOBTM_surfaceRotation_four
