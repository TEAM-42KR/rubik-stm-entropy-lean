import RubikSTM.Proofs.Rectangles.ActsPairAppend
import RubikSTM.Definitions.Rectangles.PayloadInterface
set_option autoImplicit false

theorem RubikRectangle.actsPair_append :
    ∀ {n : ℕ} (a b : Fin n) (hb : 0 < b.val ∧ b.val + 1 < n) (u v : List (Rubik.Move n)) (g h : RubikPayload.Pair) (hu : RubikRectangle.ActsPair a b hb u g) (hv : RubikRectangle.ActsPair a b hb v h), RubikRectangle.ActsPair a b hb (u ++ v) (h * g) :=
  @proof_RubikRectangle_actsPair_append
