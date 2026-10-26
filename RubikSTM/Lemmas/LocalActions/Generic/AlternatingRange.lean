import RubikSTM.Proofs.LocalActions.Generic.AlternatingRange
import RubikSTM.Definitions.LocalActions.Generic.ModelEval
set_option autoImplicit false

theorem RubikLocal.Generic.alternating_range :
    alternatingGroup (Fin 24) ≤ RubikLocal.Generic.modelEval.range :=
  @proof_RubikLocal_Generic_alternating_range
