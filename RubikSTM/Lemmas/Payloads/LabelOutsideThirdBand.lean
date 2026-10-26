import RubikSTM.Proofs.Payloads.LabelOutsideThirdBand
import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
set_option autoImplicit false

theorem RubikPayload.labelOutsideThirdBand :
    ∀ {n : ℕ} {a b c : Fin n} (hg : RubikGeometry.Generic n a b)
  (hc : RubikPayload.Half c) (hca : c ≠ a) (hcb : c ≠ b) (i : Fin 24), ¬ RubikBand.Band c (RubikGeometry.lab a b i) :=
  @proof_RubikPayload_labelOutsideThirdBand
