import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open Rubik RubikGeometry
theorem proof_RubikGeometry_F_three_t0 : Equiv.Perm.IsThreeCycle t0 := by
  apply card_support_eq_three_iff.mp
  decide
