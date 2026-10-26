import RubikSTM.Proofs.Payloads.InverseWordPermutation
import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
set_option autoImplicit false

theorem RubikPayload.inverseWordPermutation :
    ∀ {n : ℕ} (w : List (Rubik.Move n)), RubikBand.wordPerm (RubikPayload.inverseWord w) = (RubikBand.wordPerm w)⁻¹ ∧
    (RubikPayload.inverseWord w).length = w.length :=
  @proof_RubikPayload_inverseWordPermutation
