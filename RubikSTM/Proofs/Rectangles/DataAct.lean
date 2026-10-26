import RubikSTM.Definitions.Rectangles.PayloadInterface
set_option autoImplicit false

theorem proof_RubikRectangle_data_act (g : RubikPayload.Pair) (x : RubikChannel.Paired.State) :
    RubikRectangle.data (RubikChannel.Colour.pairAction RubikChannel.Paired.Seed g x) =
      RubikRectangle.rawAction g (RubikRectangle.data x) := by rfl

#print axioms proof_RubikRectangle_data_act
