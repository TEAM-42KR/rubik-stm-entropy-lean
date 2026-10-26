import RubikSTM.Proofs.Rectangles.RectanglesInvariant
import RubikSTM.Definitions.Rectangles.PayloadInterface
set_option autoImplicit false

theorem RubikRectangle.rectangles_invariant :
    ∀ {n : ℕ} (X Y : Finset (Fin n)) (w : List (Rubik.Move n)) (s : Rubik.Sticker n), RubikPayload.Rectangles X Y (RubikBand.wordPerm w s) ↔ RubikPayload.Rectangles X Y s :=
  @proof_RubikRectangle_rectangles_invariant
