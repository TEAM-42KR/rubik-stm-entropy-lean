import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
import RubikSTM.Lemmas.Rectangles.ReachableView
import RubikSTM.Lemmas.OBTM.Compiler.CommonLabels
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_common_reachable_view {n : ℕ} {a b : Fin n}
  (hg : RubikGeometry.Generic n a b) (hb : 0 < b.val ∧ b.val+1 < n) (c : Rubik.Position n) :
  ∃ x : RubikChannel.Paired.State, RubikRectangle.data x = RubikOBTMCompiler.commonView c.val a b := by
  obtain ⟨x,hx⟩ := RubikRectangle.reachable_view hg hb c
  refine ⟨x,hx.trans ?_⟩
  apply Prod.ext
  · funext i
    exact congrArg c.val (RubikOBTMCompiler.common_labels hg hb i).1.symm
  · funext i
    exact congrArg c.val (RubikOBTMCompiler.common_labels hg hb i).2.symm

#print axioms proof_RubikOBTMCompiler_common_reachable_view
