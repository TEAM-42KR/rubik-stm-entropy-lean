import RubikSTM.Proofs.OBTM.Compiler.NativeOddLayout
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
set_option autoImplicit false

theorem RubikOBTMCompiler.native_odd_layout :
    ∀ {n : ℕ} (X : Finset (Fin n)) {k : ℕ}
  (hk : 0 < k), Nonempty (RubikOBTMCompiler.OddLayout X k) :=
  @proof_RubikOBTMCompiler_native_odd_layout
