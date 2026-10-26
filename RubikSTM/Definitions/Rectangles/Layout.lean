import RubikSTM.Definitions.Rectangles.ColumnRealizes
set_option autoImplicit false

namespace RubikRectangle

structure Layout {n : ℕ} (X : Finset (Fin n)) (k : ℕ) where
  blocks : ℕ
  mod_four : blocks % 4 = 1
  bound : blocks ≤ rowCeil X.card k + 3
  owner : Fin n → Fin blocks
  row : Fin n → Fin k
  injective : ∀ a ∈ X, ∀ b ∈ X, owner a = owner b → row a = row b → a = b

def Layout.rows {n k : ℕ} {X : Finset (Fin n)} (P : Layout X k) (j : Fin P.blocks) : Finset (Fin n) :=
  X.filter (fun a => P.owner a = j)

end RubikRectangle
