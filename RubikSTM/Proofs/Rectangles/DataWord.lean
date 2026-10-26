import RubikSTM.Definitions.Rectangles.PayloadInterface
import RubikSTM.Lemmas.Rectangles.DataAct
set_option autoImplicit false

open RubikRectangle

theorem proof_RubikRectangle_data_word (cs : List RubikChannel.Paired.Letter) (x : RubikChannel.Paired.State) :
    data (cs.foldl (fun x c => RubikChannel.Paired.act c x) x) =
      rawAction ((cs.map (fun c => c.val)).reverse.prod) (data x) := by
  induction cs generalizing x with
  | nil => rfl
  | cons c cs ih =>
    rw [List.foldl_cons, ih]
    change rawAction _ (data (RubikChannel.Colour.pairAction RubikChannel.Paired.Seed c.val x)) = _
    rw [RubikRectangle.data_act]
    simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton]
    rfl

#print axioms proof_RubikRectangle_data_word
