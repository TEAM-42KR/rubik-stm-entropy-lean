import Mathlib
import RubikSTM.Definitions.Construction.Control.Physical.ActualMoves
import RubikSTM.Definitions.OrbitGeometry.GenPerm
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open Rubik RubikConstruction.Control RubikConstruction.Control.Physical
theorem proof_RubikConstruction_Control_Physical_labels_eq_T {n : ℕ} (a b : Fin n) (i : Fin 24) :
    lab a b i = RubikGeometry.lab a b i := by
  rfl
