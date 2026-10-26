import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeCoalescedWord
import RubikSTM.Lemmas.OBTM.BlockPowerApply
import RubikSTM.Lemmas.OBTM.SurfaceRotationFour
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_block_quarter_four {n : ℕ} (a : Rubik.Axis) (side : Bool) (k : Fin (n-1)) :
  RubikOBTM.blockQuarter n a side k ^ 4 = 1 := by
  apply Equiv.ext
  intro s
  rw [RubikOBTM.block_power_apply,RubikOBTM.surfaceRotation_four]
  simp

#print axioms proof_RubikOBTMCompiler_block_quarter_four
