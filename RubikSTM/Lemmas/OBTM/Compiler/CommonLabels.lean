import RubikSTM.Proofs.OBTM.Compiler.CommonLabels
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
set_option autoImplicit false

theorem RubikOBTMCompiler.common_labels :
    ∀ {n : ℕ} {a b : Fin n}
  (hg : RubikGeometry.Generic n a b) (hb : 0 < b.val ∧ b.val+1 < n) (i : Fin 24), RubikOBTM.Band.plus a b i = RubikGeometry.lab a b i ∧
    RubikOBTM.Band.minus a b i = RubikOrbit.minusLab a b hb i :=
  @proof_RubikOBTMCompiler_common_labels
