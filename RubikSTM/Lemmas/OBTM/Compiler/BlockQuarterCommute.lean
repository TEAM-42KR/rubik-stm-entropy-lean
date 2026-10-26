import RubikSTM.Proofs.OBTM.Compiler.BlockQuarterCommute
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeCoalescedWord
set_option autoImplicit false

theorem RubikOBTMCompiler.block_quarter_commute :
    ∀ {n : ℕ} (a : Rubik.Axis) (side₁ side₂ : Bool) (k l : Fin (n-1)), Commute (RubikOBTM.blockQuarter n a side₁ k) (RubikOBTM.blockQuarter n a side₂ l) :=
  @proof_RubikOBTMCompiler_block_quarter_commute
