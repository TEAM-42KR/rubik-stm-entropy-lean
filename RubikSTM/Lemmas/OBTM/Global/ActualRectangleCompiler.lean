import RubikSTM.Proofs.OBTM.Global.ActualRectangleCompiler
import RubikSTM.Definitions.OBTM.Global.RectangleCompiler
set_option autoImplicit false

theorem RubikOBTM.Global.actual_rectangle_compiler :
    RubikOBTM.Global.RectangleCompiler :=
  @proof_RubikOBTM_Global_actual_rectangle_compiler
