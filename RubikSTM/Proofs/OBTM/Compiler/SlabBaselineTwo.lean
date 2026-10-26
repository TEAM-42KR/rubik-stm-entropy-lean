import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeCoalescedWord
import RubikSTM.Lemmas.OBTM.Compiler.NativeCoalescedAction
import RubikSTM.Lemmas.OBTM.Compiler.HalfPrefixWordTwo
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_slab_baseline_two {n : ℕ} (a : Rubik.Axis) (side : Bool) (lower : Fin (n-1))
  (B : List (Fin (n-1))) : RubikOBTMCompiler.slabBaseline a side lower B ^ 2 = 1 := by
  rw [← RubikOBTMCompiler.native_coalesced_action a side lower B]
  by_cases he : B.length%2=0
  · simpa [RubikOBTMCompiler.nativeCoalescedWord,he] using
      RubikOBTMCompiler.half_prefix_word_two a side B
  · simpa [RubikOBTMCompiler.nativeCoalescedWord,he] using
      RubikOBTMCompiler.half_prefix_word_two a side (lower::B)

#print axioms proof_RubikOBTMCompiler_slab_baseline_two
