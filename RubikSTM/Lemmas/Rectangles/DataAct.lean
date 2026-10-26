import RubikSTM.Proofs.Rectangles.DataAct
import RubikSTM.Definitions.Rectangles.PayloadInterface
set_option autoImplicit false

theorem RubikRectangle.data_act :
    ∀ (g : RubikPayload.Pair) (x : RubikChannel.Paired.State), RubikRectangle.data (RubikChannel.Colour.pairAction RubikChannel.Paired.Seed g x) = RubikRectangle.rawAction g (RubikRectangle.data x) :=
  @proof_RubikRectangle_data_act
