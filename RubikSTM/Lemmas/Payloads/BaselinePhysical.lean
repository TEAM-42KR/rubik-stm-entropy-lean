import RubikSTM.Proofs.Payloads.BaselinePhysical
import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
set_option autoImplicit false

theorem RubikPayload.baselinePhysical :
    ∀ {n : ℕ} (Y : Finset (Fin n)), (RubikPayload.baselineWord Y).length = Y.card ∧
  ∀ s : Rubik.Sticker n, ¬ RubikBand.Bands Y s → RubikPayload.columnBaseline Y s = s :=
  @proof_RubikPayload_baselinePhysical
