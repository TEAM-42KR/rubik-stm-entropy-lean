import RubikSTM.Definitions.OBTM.Band.CleanAction
import RubikSTM.Lemmas.OBTM.Band.WordPermAppend
import RubikSTM.Lemmas.OBTM.SliceTwoBlocks
set_option autoImplicit false
open Rubik RubikOBTM RubikOBTM.Band

theorem proof_RubikOBTM_Band_stm_word_blocks {n : ℕ} (hn : 2 ≤ n) (ms : List (Move n)) :
    ∃ w : List (BlockMove n), w.length ≤ 2*ms.length ∧ wordPerm w = RubikBand.wordPerm ms := by
  induction ms with
  | nil => exact ⟨[],by simp,rfl⟩
  | cons m ms ih =>
    obtain ⟨w,hw,he⟩ := ih
    obtain ⟨b,hb,hbe⟩ := RubikOBTM.slice_two_blocks hn m
    refine ⟨b++w,?_,?_⟩
    · simp only [List.length_append,List.length_cons]
      omega
    · rw [wordPerm_append,he]
      change RubikBand.wordPerm ms * ((b.map blockPermutation).reverse.prod) = _
      rw [hbe]
      simp [RubikBand.wordPerm,List.reverse_cons]
