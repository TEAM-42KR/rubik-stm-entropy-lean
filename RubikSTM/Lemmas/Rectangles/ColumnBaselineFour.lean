import RubikSTM.Proofs.Rectangles.ColumnBaselineFour
import RubikSTM.Definitions.Rectangles.PayloadInterface
set_option autoImplicit false

theorem RubikRectangle.columnBaseline_four :
    ∀ {n : ℕ} (Y : Finset (Fin n)), RubikPayload.columnBaseline Y ^ 4 = 1 :=
  @proof_RubikRectangle_columnBaseline_four
