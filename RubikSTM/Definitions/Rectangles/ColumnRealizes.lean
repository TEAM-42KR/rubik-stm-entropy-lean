import RubikSTM.Definitions.Rectangles.Framed
set_option autoImplicit false

namespace RubikRectangle

def ColumnRealizes {n : ℕ} (A Y : Finset (Fin n))
    (g : Fin n → Fin n → RubikPayload.Pair) (w : List (Rubik.Move n)) : Prop :=
  (∀ a ∈ A, ∀ b ∈ Y, ∀ hb : 0 < b.val ∧ b.val + 1 < n,
    ActsPair a b hb w (g a b)) ∧
  (∀ s : Rubik.Sticker n, ¬ RubikPayload.Rectangles A Y s →
    RubikBand.wordPerm w s = RubikPayload.columnBaseline Y s)

end RubikRectangle
