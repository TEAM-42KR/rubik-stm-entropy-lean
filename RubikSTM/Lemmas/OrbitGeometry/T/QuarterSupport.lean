import RubikSTM.Proofs.OrbitGeometry.T.QuarterSupport
import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
set_option autoImplicit false
open Rubik

theorem RubikGeometry.T.quarter_support :
    ∀ {n : ℕ} (ax : Axis) (l : Fin n) (s : Sticker n)
    (h : movePermutation (ax, l, 0) s ≠ s), coordinate s.val.1 ax = l :=
  @proof_RubikGeometry_T_quarter_support
