import RubikSTM.Proofs.Rectangles.LayoutExists
import RubikSTM.Definitions.Rectangles.Layout
set_option autoImplicit false

theorem RubikRectangle.layout_exists :
    ∀ {n : ℕ} (X : Finset (Fin n)) {k : ℕ} (hk : 0 < k), Nonempty (RubikRectangle.Layout X k) :=
  @proof_RubikRectangle_layout_exists
