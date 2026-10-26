import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
import RubikSTM.Lemmas.Payloads.WordFlipCommute
import RubikSTM.Lemmas.Payloads.AllowedAvoidsColumn
set_option autoImplicit false

theorem proof_RubikPayload_commonMinusAction {n : ℕ} {a b : Fin n} (hg : RubikGeometry.Generic n a b)
  (hb : 0 < b.val ∧ b.val + 1 < n) (w : List (Rubik.Move n))
  (hw : RubikBand.AllowedControl a w) (σ : Equiv.Perm (Fin 24))
  (hplus : ∀ i, RubikBand.wordPerm w (RubikGeometry.lab a b i) = RubikGeometry.lab a b (σ i)) :
  ∀ i, RubikBand.wordPerm w (RubikOrbit.minusLab a b hb i) =
    RubikOrbit.minusLab a b hb (σ i) := by
  intro i
  have hc := RubikPayload.wordFlipCommute b hb w (RubikPayload.allowedAvoidsColumn hg w hw)
  have he := congrArg (fun p : Equiv.Perm (Rubik.Sticker n) => p (RubikGeometry.lab a b i)) hc.eq
  simpa only [Equiv.Perm.mul_apply, hplus i, RubikOrbit.minusLab] using he

#print axioms proof_RubikPayload_commonMinusAction
