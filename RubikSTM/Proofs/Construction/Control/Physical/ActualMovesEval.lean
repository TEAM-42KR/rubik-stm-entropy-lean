import Mathlib
import RubikSTM.Definitions.Construction.Control.Physical.ActualMoves
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Lemmas.Construction.Control.Physical.ChronologicalAlgebra
import RubikSTM.Lemmas.Construction.Control.Physical.SignedMoveEval
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open Rubik RubikConstruction.Control RubikConstruction.Control.Physical
theorem proof_RubikConstruction_Control_Physical_actual_moves_eval {n : ℕ} (a : Fin n) (letters : List SignedLetter) :
    chronological (actualMoves a letters) = physicalEval a (FreeGroup.mk letters) := by
  rw [chronological_algebra]
  simp only [actualMoves, ← List.map_reverse, List.reverse_reverse, List.map_map]
  simp [physicalEval, FreeGroup.lift_mk, signed_move_eval, Function.comp_def, cond_eq_ite]
