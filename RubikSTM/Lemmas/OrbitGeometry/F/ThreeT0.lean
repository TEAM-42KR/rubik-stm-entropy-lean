import RubikSTM.Proofs.OrbitGeometry.F.ThreeT0
import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
set_option autoImplicit false
open Rubik

theorem RubikGeometry.F.three_t0 :
    Equiv.Perm.IsThreeCycle t0 :=
  @proof_RubikGeometry_F_three_t0
