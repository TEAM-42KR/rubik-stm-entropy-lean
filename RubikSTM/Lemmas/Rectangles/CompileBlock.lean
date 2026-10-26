import RubikSTM.Proofs.Rectangles.CompileBlock
import RubikSTM.Definitions.Rectangles.ColumnRealizes
set_option autoImplicit false
open RubikRectangle RubikPayload
open scoped Classical

theorem RubikRectangle.compileBlock :
    ∀ (C : ℕ) (hP : PayloadInterface C) {n k : ℕ}
    (A Y : Finset (Fin n)) (hAY : Admissible A Y) (hAk : A.card ≤ k)
    (row : Fin n → Fin k) (D : Finset (Fin k → RubikChannel.Paired.Letter))
    (choice : Fin n → Fin k → RubikChannel.Paired.Letter)
    (hchoice : ∀ b ∈ Y, choice b ∈ D), ∃ w : List (Rubik.Move n),
      w.length ≤ Y.card + C * (k + 1) * D.card ∧
        ColumnRealizes A Y (fun a b => (choice b (row a)).val) w :=
  @proof_RubikRectangle_compileBlock
