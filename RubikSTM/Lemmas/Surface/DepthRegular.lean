import RubikSTM.Proofs.Surface.DepthRegular
import RubikSTM.Definitions.Surface.GenericRange
set_option autoImplicit false
open Rubik RubikGeometry RubikGlobal
open scoped Classical

theorem RubikGlobal.depth_regular :
    ∀ {n : ℕ} (i : RubikGlobal.I n), RubikExceptional.Regular n (RubikGlobal.depth i) ∧ RubikWing.Admissible n (RubikGlobal.depth i) :=
  @proof_RubikGlobal_depth_regular
