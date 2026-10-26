import RubikSTM.Proofs.OBTM.Compiler.RectangleOfNativePulse
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
set_option autoImplicit false

theorem RubikOBTMCompiler.rectangle_of_native_pulse :
    ∀ (hP : ∃ C : ℕ, RubikOBTMCompiler.NativePulseInterface C), RubikOBTM.Global.RectangleCompiler :=
  @proof_RubikOBTMCompiler_rectangle_of_native_pulse
