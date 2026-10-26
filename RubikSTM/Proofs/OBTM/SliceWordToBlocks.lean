import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Lemmas.OBTM.SliceTwoBlocks
import RubikSTM.Lemmas.OBTM.BlockWordAction
set_option autoImplicit false

theorem proof_RubikOBTM_sliceWord_to_blocks {n : ℕ} (hn : 2 ≤ n) (w : List (Rubik.Move n)) :
    ∃ v : List (RubikOBTM.BlockMove n), v.length ≤ 2 * w.length ∧
      ∀ c : Rubik.Colouring n, RubikOBTM.applyBlockWord v c = Rubik.applyWord w c := by
  induction w with
  | nil => exact ⟨[], by simp, by intro c; rfl⟩
  | cons m w ih =>
    obtain ⟨v, hv, he⟩ := ih
    obtain ⟨b, hb, hperm⟩ := RubikOBTM.slice_two_blocks hn m
    refine ⟨b ++ v, ?_, ?_⟩
    · simp only [List.length_append, List.length_cons]
      omega
    · intro c
      have hsingle : RubikOBTM.applyBlockWord b c = Rubik.applyMove m c := by
        rw [RubikOBTM.blockWord_action, hperm]
        rfl
      change (b ++ v).foldl (fun state m => RubikOBTM.applyBlock m state) c = _
      rw [List.foldl_append]
      change RubikOBTM.applyBlockWord v (RubikOBTM.applyBlockWord b c) = _
      rw [hsingle, he]
      rfl
