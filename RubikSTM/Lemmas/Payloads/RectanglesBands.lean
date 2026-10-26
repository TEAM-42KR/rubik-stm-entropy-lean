import RubikSTM.Proofs.Payloads.RectanglesBands
import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
set_option autoImplicit false

theorem RubikPayload.rectanglesBands :
    ∀ {n : ℕ} {A Y : Finset (Fin n)} (h : RubikPayload.Admissible A Y)
  (s : Rubik.Sticker n), RubikPayload.Rectangles A Y s ↔
    RubikBand.Bands A s ∧ RubikBand.Bands Y s :=
  @proof_RubikPayload_rectanglesBands
