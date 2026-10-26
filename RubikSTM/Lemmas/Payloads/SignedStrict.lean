import RubikSTM.Proofs.Payloads.SignedStrict
import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
set_option autoImplicit false

theorem RubikPayload.signedStrict :
    ∀ {n : ℕ} (a : Fin n) (ha : RubikPayload.Half a)
  (letters : List RubikConstruction.Control.Physical.SignedLetter)
  (hd : RubikConstruction.Control.deletion (FreeGroup.mk letters) = 1), RubikBand.StrictControl a (RubikConstruction.Control.Physical.actualMoves a letters) :=
  @proof_RubikPayload_signedStrict
