import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeCoalescedWord
import RubikSTM.Lemmas.OBTM.Compiler.CoalescedSlab
import RubikSTM.Lemmas.OBTM.Compiler.LowerHalfCoalesces
import RubikSTM.Lemmas.OBTM.Compiler.BlockQuarterCommute
import RubikSTM.Lemmas.OBTM.Compiler.BlockQuarterFour
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_native_coalesced_action {n : ℕ} (a : Rubik.Axis) (side : Bool) (lower : Fin (n-1))
  (B : List (Fin (n-1))) :
  RubikOBTM.Band.wordPerm (RubikOBTMCompiler.nativeCoalescedWord a side lower B) =
    RubikOBTMCompiler.slabBaseline a side lower B := by
  unfold RubikOBTMCompiler.slabBaseline
  rw [RubikOBTMCompiler.coalesced_slab (fun b => RubikOBTM.blockQuarter n a side b)
    (RubikOBTM.blockQuarter n a side lower) B (by
      intro b hb; exact RubikOBTMCompiler.block_quarter_commute a side side lower b)]
  rw [RubikOBTMCompiler.lower_half_coalesces _ (RubikOBTMCompiler.block_quarter_four a side lower)]
  by_cases he : B.length%2=0
  · simp [RubikOBTMCompiler.nativeCoalescedWord,he,RubikOBTM.Band.wordPerm,
      RubikOBTMCompiler.halfPrefix,RubikOBTM.blockPermutation,List.map_map,Function.comp_def]
  · have ho : B.length%2=1 := by omega
    simp [RubikOBTMCompiler.nativeCoalescedWord,he,ho,RubikOBTM.Band.wordPerm,
      RubikOBTMCompiler.halfPrefix,RubikOBTM.blockPermutation,List.map_map,Function.comp_def]

#print axioms proof_RubikOBTMCompiler_native_coalesced_action
