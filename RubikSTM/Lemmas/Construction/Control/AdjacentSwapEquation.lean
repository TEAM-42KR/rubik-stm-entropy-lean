import RubikSTM.Proofs.Construction.Control.AdjacentSwapEquation
import Mathlib
import RubikSTM.Definitions.Construction.Control.K
set_option autoImplicit false

theorem RubikConstruction.Control.adjacent_swap_equation :
    ∀ (i : Fin 23), RubikConstruction.Control.wordEval (RubikConstruction.Control.adjacentPath i) * Equiv.swap (9 : Fin 24) 20 * (RubikConstruction.Control.wordEval (RubikConstruction.Control.adjacentPath i))⁻¹ = Equiv.swap i.castSucc i.succ :=
  @proof_RubikConstruction_Control_adjacent_swap_equation
