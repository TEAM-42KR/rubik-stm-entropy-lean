import RubikSTM.Proofs.Construction.Control.BaseSwapEquation
import Mathlib
import RubikSTM.Definitions.Construction.Control.K
set_option autoImplicit false

theorem RubikConstruction.Control.base_swap_equation :
    RubikConstruction.Control.baseSwapWitness = Equiv.swap (9 : Fin 24) 20 :=
  @proof_RubikConstruction_Control_base_swap_equation
