import Mathlib
import RubikSTM.Definitions.Construction.Control.Physical.ActualMoves
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Definitions.Wings.SolverWord
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open Rubik RubikConstruction.Control RubikConstruction.Control.Physical
theorem proof_RubikConstruction_Control_Physical_quarter_inverse (n : ℕ) (ax : Axis) (layer : Fin n) :
    movePermutation (ax, layer, 2) = (movePermutation (ax, layer, 0))⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  change sliceQuarter n ax layer ^ 3 * sliceQuarter n ax layer = 1
  rw [← pow_succ, sliceQuarter_order_four]
