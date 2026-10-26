import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
import RubikSTM.Lemmas.OBTM.Compiler.NativePulse
import RubikSTM.Lemmas.OBTM.Compiler.RectangleOfNativePulse
set_option autoImplicit false

theorem proof_RubikOBTM_Global_actual_rectangle_compiler : RubikOBTM.Global.RectangleCompiler := by
  exact RubikOBTMCompiler.rectangle_of_native_pulse RubikOBTMCompiler.native_pulse
