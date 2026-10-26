import RubikSTM.Proofs.LocalActions.Generic.LocalActionMul
import RubikSTM.Definitions.LocalActions.Generic.ModelEval
set_option autoImplicit false
open RubikLocal.Generic

theorem RubikLocal.Generic.local_action_mul :
    ∀ {n : ℕ} (a b : Fin n) (τ υ : RubikLocal.Generic.Perm) (g h : Equiv.Perm (Rubik.Sticker n)) (hg : RubikLocal.Generic.LocalAction a b τ g) (hh : RubikLocal.Generic.LocalAction a b υ h), RubikLocal.Generic.LocalAction a b (τ * υ) (g * h) :=
  @proof_RubikLocal_Generic_local_action_mul
