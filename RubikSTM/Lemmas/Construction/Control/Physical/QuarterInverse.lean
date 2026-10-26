import RubikSTM.Proofs.Construction.Control.Physical.QuarterInverse
import RubikSTM.Definitions.Geometry.StmGraph
set_option autoImplicit false

theorem RubikConstruction.Control.Physical.quarter_inverse :
    ∀ (n : ℕ) (ax : Rubik.Axis) (layer : Fin n), Rubik.movePermutation (ax, layer, 2) = (Rubik.movePermutation (ax, layer, 0))⁻¹ :=
  @proof_RubikConstruction_Control_Physical_quarter_inverse
