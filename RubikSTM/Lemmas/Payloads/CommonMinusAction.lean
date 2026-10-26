import RubikSTM.Proofs.Payloads.CommonMinusAction
import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
set_option autoImplicit false

theorem RubikPayload.commonMinusAction :
    ∀ {n : ℕ} {a b : Fin n} (hg : RubikGeometry.Generic n a b)
  (hb : 0 < b.val ∧ b.val + 1 < n) (w : List (Rubik.Move n))
  (hw : RubikBand.AllowedControl a w) (σ : Equiv.Perm (Fin 24))
  (hplus : ∀ i, RubikBand.wordPerm w (RubikGeometry.lab a b i) = RubikGeometry.lab a b (σ i)), ∀ i, RubikBand.wordPerm w (RubikOrbit.minusLab a b hb i) =
    RubikOrbit.minusLab a b hb (σ i) :=
  @proof_RubikPayload_commonMinusAction
