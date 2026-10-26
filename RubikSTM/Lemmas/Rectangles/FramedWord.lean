import RubikSTM.Proofs.Rectangles.FramedWord
import RubikSTM.Definitions.Rectangles.Framed
set_option autoImplicit false
open RubikRectangle RubikPayload

theorem RubikRectangle.framed_word :
    ∀ {n L t : ℕ} (X Y : Finset (Fin n)) (hXY : Admissible X Y)
    (owner : X → Fin t) (F : Fin L → X → Y → Pair)
    (ws : Fin L → Fin t → List (Rubik.Move n)) (hframe : Framed X Y owner F ws)
    (c d : Rubik.Colouring n) (ht : t % 4 = 1) (hL : L % 4 = 0)
    (hraw : ∀ (a : X) (b : Y) (hb : 0 < b.val.val ∧ b.val.val + 1 < n),
      rawAction ((List.ofFn (fun i => F i a b)).reverse.prod)
        (rawAction (B ^ ((owner a).val % 4)) (view c a.val b.val hb)) =
      rawAction (B ^ ((owner a).val % 4)) (view d a.val b.val hb))
    (cost : ℕ) (hcost : ∀ i j, (ws i j).length ≤ cost), (program ws).length ≤ L * t * cost ∧
      (∀ s : Rubik.Sticker n, Rectangles X Y s → Rubik.applyWord (program ws) c s = d s) ∧
      (∀ s : Rubik.Sticker n, ¬ Rectangles X Y s → RubikBand.wordPerm (program ws) s = s) :=
  @proof_RubikRectangle_framed_word
