import RubikSTM.Proofs.Rectangles.DataWord
import RubikSTM.Definitions.Rectangles.PayloadInterface
set_option autoImplicit false

theorem RubikRectangle.data_word :
    ∀ (cs : List RubikChannel.Paired.Letter) (x : RubikChannel.Paired.State), RubikRectangle.data (cs.foldl (fun x c => RubikChannel.Paired.act c x) x) = RubikRectangle.rawAction ((cs.map (fun c => c.val)).reverse.prod) (RubikRectangle.data x) :=
  @proof_RubikRectangle_data_word
