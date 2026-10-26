import RubikSTM.Proofs.Payloads.ChronologicalWord
import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
set_option autoImplicit false

theorem RubikPayload.chronologicalWord :
    ∀ {n : ℕ} (w : List (Rubik.Move n)), RubikConstruction.Control.Physical.chronological w = RubikBand.wordPerm w :=
  @proof_RubikPayload_chronologicalWord
