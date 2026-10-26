import RubikSTM.Definitions.Rectangles.PayloadInterface
import RubikSTM.Lemmas.Rectangles.ActsPairAppend
set_option autoImplicit false

open RubikRectangle RubikPayload

theorem proof_RubikRectangle_actsPair_flatten {n : ℕ} (a b : Fin n) (hb : 0 < b.val ∧ b.val + 1 < n)
    (ws : List (List (Rubik.Move n))) (gs : List Pair)
    (h : List.Forall₂ (fun w g => ActsPair a b hb w g) ws gs) :
    ActsPair a b hb ws.flatten gs.reverse.prod := by
  induction h with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | @cons w g ws gs hwh htail ih =>
    simpa only [List.flatten_cons, List.reverse_cons, List.prod_append,
      List.prod_singleton] using RubikRectangle.actsPair_append a b hb w ws.flatten
        g gs.reverse.prod hwh ih

#print axioms proof_RubikRectangle_actsPair_flatten
