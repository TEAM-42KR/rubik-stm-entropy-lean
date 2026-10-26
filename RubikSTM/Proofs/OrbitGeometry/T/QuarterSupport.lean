import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open Rubik RubikGeometry
theorem proof_RubikGeometry_T_quarter_support {n : ℕ} (ax : Axis) (l : Fin n) (s : Sticker n)
    (h : movePermutation (ax, l, 0) s ≠ s) : coordinate s.val.1 ax = l := by
  by_contra he
  apply h
  simp [movePermutation, sliceQuarter, he]
