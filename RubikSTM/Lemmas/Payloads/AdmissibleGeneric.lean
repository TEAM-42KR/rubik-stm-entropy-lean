import RubikSTM.Proofs.Payloads.AdmissibleGeneric
import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
set_option autoImplicit false

theorem RubikPayload.admissibleGeneric :
    ∀ {n : ℕ} {A Y : Finset (Fin n)} (h : RubikPayload.Admissible A Y)
  {a b : Fin n} (ha : a ∈ A) (hb : b ∈ Y), RubikGeometry.Generic n a b :=
  @proof_RubikPayload_admissibleGeneric
