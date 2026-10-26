import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Definitions.LocalActions.Generic.ModelEval
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open Rubik RubikGeometry
open RubikLocal.Generic RubikConstruction.Control.Physical
theorem proof_RubikLocal_Generic_chronological_append {n : ℕ} (u v : List (Move n)) :
    chronological (u ++ v) = chronological v * chronological u := by
  induction u with
  | nil => simp [chronological]
  | cons m u ih => simp [chronological, ih, mul_assoc]
