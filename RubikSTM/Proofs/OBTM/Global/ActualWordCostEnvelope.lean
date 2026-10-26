import RubikSTM.Definitions.OBTM.Global.RectangleCompiler
import RubikSTM.Lemmas.OBTM.Global.ActualRectangleCompiler
import RubikSTM.Lemmas.OBTM.Global.ActualBookSupply
import RubikSTM.Lemmas.OBTM.Global.WordEnvelopeOfCompilers
set_option autoImplicit false

theorem proof_RubikOBTM_Global_actual_word_cost_envelope : RubikOBTM.Global.WordCostEnvelope :=
  RubikOBTM.Global.wordEnvelope_of_compilers
    RubikOBTM.Global.actual_rectangle_compiler RubikOBTM.Global.actual_book_supply
