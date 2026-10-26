import RubikSTM.Proofs.OBTM.Global.ActualBookSupply
import RubikSTM.Definitions.OBTM.Global.RectangleCompiler
set_option autoImplicit false

theorem RubikOBTM.Global.actual_book_supply :
    RubikOBTM.Global.BookSupply :=
  @proof_RubikOBTM_Global_actual_book_supply
