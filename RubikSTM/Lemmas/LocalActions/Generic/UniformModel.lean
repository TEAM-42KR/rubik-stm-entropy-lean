import RubikSTM.Proofs.LocalActions.Generic.UniformModel
import RubikSTM.Definitions.LocalActions.Generic.ModelEval
set_option autoImplicit false
open RubikLocal.Generic

theorem RubikLocal.Generic.uniform_model :
    ∃ M : ℕ, ∀ τ : Equiv.Perm (Fin 24), τ ∈ alternatingGroup (Fin 24) → ∃ ts : List RubikLocal.Generic.Token, ts.length ≤ M ∧ RubikLocal.Generic.evalTokens ts = τ :=
  @proof_RubikLocal_Generic_uniform_model
