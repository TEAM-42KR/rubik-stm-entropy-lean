import RubikSTM.Proofs.LocalActions.Generic.LocalActionInv
import RubikSTM.Definitions.LocalActions.Generic.ModelEval
set_option autoImplicit false
open RubikLocal.Generic

theorem RubikLocal.Generic.local_action_inv :
    ∀ {n : ℕ} (a b : Fin n) (τ : RubikLocal.Generic.Perm) (g : Equiv.Perm (Rubik.Sticker n)) (hg : RubikLocal.Generic.LocalAction a b τ g), RubikLocal.Generic.LocalAction a b τ⁻¹ g⁻¹ :=
  @proof_RubikLocal_Generic_local_action_inv
