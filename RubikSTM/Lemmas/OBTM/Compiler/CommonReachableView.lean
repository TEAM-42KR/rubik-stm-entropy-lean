import RubikSTM.Proofs.OBTM.Compiler.CommonReachableView
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
set_option autoImplicit false

theorem RubikOBTMCompiler.common_reachable_view :
    ∀ {n : ℕ} {a b : Fin n}
  (hg : RubikGeometry.Generic n a b) (hb : 0 < b.val ∧ b.val+1 < n) (c : Rubik.Position n), ∃ x : RubikChannel.Paired.State, RubikRectangle.data x = RubikOBTMCompiler.commonView c.val a b :=
  @proof_RubikOBTMCompiler_common_reachable_view
