import RubikSTM.Proofs.LocalActions.Generic.ModelEvalMk
import RubikSTM.Definitions.LocalActions.Generic.ModelEval
set_option autoImplicit false
open RubikLocal.Generic

theorem RubikLocal.Generic.model_eval_mk :
    ∀ (ts : List RubikLocal.Generic.Token), RubikLocal.Generic.modelEval (FreeGroup.mk ts) = RubikLocal.Generic.evalTokens ts :=
  @proof_RubikLocal_Generic_model_eval_mk
