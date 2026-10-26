import Mathlib
import RubikSTM.Definitions.Construction.Control.K
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open RubikConstruction.Control
theorem proof_RubikConstruction_Control_adjacent_swap_equation (i : Fin 23) :
    wordEval (adjacentPath i) * Equiv.swap (9 : Fin 24) 20 *
      (wordEval (adjacentPath i))⁻¹ = Equiv.swap i.castSucc i.succ := by
  fin_cases i <;> decide
