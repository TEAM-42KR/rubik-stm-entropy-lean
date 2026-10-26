import RubikSTM.Proofs.LocalActions.Generic.LocalActionConjugate
import RubikSTM.Definitions.LocalActions.Generic.ModelEval
set_option autoImplicit false
open RubikLocal.Generic

theorem RubikLocal.Generic.local_action_conjugate :
    ∀ {n : ℕ} (a b : Fin n) (q τ : RubikLocal.Generic.Perm) (p g : Equiv.Perm (Rubik.Sticker n)) (hp : ∀ i, p (RubikGeometry.lab a b i) = RubikGeometry.lab a b (q i)) (hg : RubikLocal.Generic.LocalAction a b τ g), RubikLocal.Generic.LocalAction a b (q * τ * q⁻¹) (p * g * p⁻¹) :=
  @proof_RubikLocal_Generic_local_action_conjugate
