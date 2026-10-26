import RubikSTM.Proofs.GlobalWords.RectangleRecolour
import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
set_option autoImplicit false

theorem RubikGlobalWord.rectangle_recolour :
    ∃ C : ℕ, ∀ (n : ℕ) (A Y : Finset (Fin n)), RubikPayload.Admissible A Y →
  ∀ (k L M : ℕ), 0 < k → 0 < L → 4 ∣ L →
  ∀ B : RubikCodebook.Book RubikChannel.Paired.Letter k L,
    RubikCodebook.CoversAll RubikChannel.Paired.act B →
    (∀ i : Fin L, (B i).card ≤ M) → ∀ c d : Rubik.Position n,
  ∃ w : List (Rubik.Move n),
    w.length ≤ L * (RubikRectangle.rowCeil A.card k+3) * (Y.card+C*(k+1)*M) ∧
    RubikGlobalWord.Recolour {s | RubikPayload.Rectangles A Y s} c.val d.val w :=
  @proof_RubikGlobalWord_rectangle_recolour
