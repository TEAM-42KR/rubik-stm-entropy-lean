import RubikSTM.Proofs.OBTM.Global.WordEnvelopeOfCompilers
import RubikSTM.Definitions.OBTM.Global.RectangleCompiler
set_option autoImplicit false

theorem RubikOBTM.Global.wordEnvelope_of_compilers :
    ∀ (hrect : RubikOBTM.Global.RectangleCompiler) (hbooks : RubikOBTM.Global.BookSupply), RubikOBTM.Global.WordCostEnvelope :=
  @proof_RubikOBTM_Global_wordEnvelope_of_compilers
