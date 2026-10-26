import RubikSTM.Proofs.OBTM.Compiler.NativePulse
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
set_option autoImplicit false

theorem RubikOBTMCompiler.native_pulse :
    ∃ C : ℕ, RubikOBTMCompiler.NativePulseInterface C :=
  @proof_RubikOBTMCompiler_native_pulse
