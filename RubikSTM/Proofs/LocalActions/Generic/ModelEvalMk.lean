import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Definitions.LocalActions.Generic.ModelEval
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open Rubik RubikGeometry
open RubikLocal.Generic RubikConstruction.Control.Physical
theorem proof_RubikLocal_Generic_model_eval_mk (ts : List Token) : modelEval (FreeGroup.mk ts) = evalTokens ts := by
  simp only [modelEval, FreeGroup.lift_mk, evalTokens]
  congr 1
  apply List.map_congr_left
  intro t _
  rcases t with ⟨q, s⟩
  cases s <;> rfl
