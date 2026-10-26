import RubikSTM.Proofs.Rectangles.LayoutRowsCard
import RubikSTM.Definitions.Rectangles.Layout
set_option autoImplicit false

theorem RubikRectangle.layout_rows_card :
    ∀ {n k : ℕ} {X : Finset (Fin n)} (P : RubikRectangle.Layout X k) (j : Fin P.blocks), (P.rows j).card ≤ k :=
  @proof_RubikRectangle_layout_rows_card
