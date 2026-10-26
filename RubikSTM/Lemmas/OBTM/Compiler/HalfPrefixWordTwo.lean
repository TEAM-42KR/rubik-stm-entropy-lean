import RubikSTM.Proofs.OBTM.Compiler.HalfPrefixWordTwo
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeCoalescedWord
set_option autoImplicit false

theorem RubikOBTMCompiler.half_prefix_word_two :
    ∀ {n : ℕ} (a : Rubik.Axis) (side : Bool) (B : List (Fin (n-1))), RubikOBTM.Band.wordPerm (B.map (RubikOBTMCompiler.halfPrefix a side)) ^ 2 = 1 :=
  @proof_RubikOBTMCompiler_half_prefix_word_two
