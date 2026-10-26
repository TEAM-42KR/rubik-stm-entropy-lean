import RubikSTM.Proofs.Rectangles.PairColouring
import RubikSTM.Definitions.Rectangles.PayloadInterface
set_option autoImplicit false

theorem RubikRectangle.pairColouring :
    ∀ {n : ℕ} (a b : Fin n) (hb : 0 < b.val ∧ b.val + 1 < n) (w : List (Rubik.Move n)) (g : RubikPayload.Pair) (h : RubikRectangle.ActsPair a b hb w g) (c : Rubik.Colouring n), RubikRectangle.view (Rubik.applyWord w c) a b hb = RubikRectangle.rawAction g (RubikRectangle.view c a b hb) :=
  @proof_RubikRectangle_pairColouring
