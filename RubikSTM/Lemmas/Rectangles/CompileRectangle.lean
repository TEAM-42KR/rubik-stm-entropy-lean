import RubikSTM.Proofs.Rectangles.CompileRectangle
import RubikSTM.Definitions.Rectangles.Layout
import RubikSTM.Definitions.GlobalWords.Region
set_option autoImplicit false
open RubikRectangle RubikPayload
open scoped Classical

theorem RubikRectangle.compile_rectangle :
    ∀ (C : ℕ) (hP : PayloadInterface C) {n : ℕ}
    (X Y : Finset (Fin n)) (hXY : Admissible X Y) (k L M : ℕ) (hk : 0 < k)
    (hL : 4 ∣ L) (Book : RubikCodebook.Book RubikChannel.Paired.Letter k L)
    (hBook : RubikCodebook.CoversAll RubikChannel.Paired.act Book)
    (hM : ∀ i, (Book i).card ≤ M) (c d : Rubik.Position n), ∃ w : List (Rubik.Move n),
      w.length ≤ L * (rowCeil X.card k + 3) * (Y.card + C * (k + 1) * M) ∧
      RubikGlobalWord.Recolour {s | Rectangles X Y s} c.val d.val w :=
  @proof_RubikRectangle_compile_rectangle
