import Mathlib
import RubikSTM.Definitions.Construction.Control.Physical.ActualMoves
import RubikSTM.Definitions.OrbitGeometry.GenPerm
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open Rubik RubikConstruction.Control RubikConstruction.Control.Physical
theorem proof_RubikConstruction_Control_Physical_chronological_algebra {n : ℕ} (ms : List (Move n)) :
    chronological ms = (ms.reverse.map movePermutation).prod := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp [chronological, List.reverse_cons, ih]
