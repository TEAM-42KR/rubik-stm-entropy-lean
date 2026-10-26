import Mathlib
import RubikSTM.Definitions.Construction.Control.K
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open RubikConstruction.Control
theorem proof_RubikConstruction_Control_base_swap_equation : baseSwapWitness = Equiv.swap (9 : Fin 24) 20 := by
  decide
