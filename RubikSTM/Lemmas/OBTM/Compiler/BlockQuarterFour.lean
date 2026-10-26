import RubikSTM.Proofs.OBTM.Compiler.BlockQuarterFour
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeCoalescedWord
set_option autoImplicit false

theorem RubikOBTMCompiler.block_quarter_four :
    ∀ {n : ℕ} (a : Rubik.Axis) (side : Bool) (k : Fin (n-1)), RubikOBTM.blockQuarter n a side k ^ 4 = 1 :=
  @proof_RubikOBTMCompiler_block_quarter_four
