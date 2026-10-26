import RubikSTM.Proofs.Rectangles.ActsPairFlatten
import RubikSTM.Definitions.Rectangles.PayloadInterface
set_option autoImplicit false

theorem RubikRectangle.actsPair_flatten :
    ∀ {n : ℕ} (a b : Fin n) (hb : 0 < b.val ∧ b.val + 1 < n) (ws : List (List (Rubik.Move n))) (gs : List RubikPayload.Pair) (h : List.Forall₂ (fun w g => RubikRectangle.ActsPair a b hb w g) ws gs), RubikRectangle.ActsPair a b hb ws.flatten gs.reverse.prod :=
  @proof_RubikRectangle_actsPair_flatten
