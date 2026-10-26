import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Lemmas.OBTM.BlockInverse
set_option autoImplicit false

theorem proof_RubikOBTM_obtmGraph_walk_word {n : ℕ} {u v : Rubik.Position n} (p : (RubikOBTM.obtmGraph n).Walk u v) :
    ∃ w : List (RubikOBTM.BlockMove n), w.length = p.length ∧
      RubikOBTM.applyBlockWord w u.val = v.val := by
  induction p with
  | nil => exact ⟨[], rfl, rfl⟩
  | @cons u v z h p ih =>
    obtain ⟨w, hwlen, hw⟩ := ih
    have hedge : ∃ m : RubikOBTM.BlockMove n, RubikOBTM.applyBlock m u.val = v.val := by
      rcases h.2 with hf | hr
      · exact hf
      · obtain ⟨m, hm⟩ := hr
        obtain ⟨r, hinv⟩ := RubikOBTM.block_inverse m
        refine ⟨r, ?_⟩
        rw [← hm]
        funext s
        change v.val ((RubikOBTM.blockPermutation m).symm ((RubikOBTM.blockPermutation r).symm s)) = v.val s
        rw [hinv]
        exact congrArg v.val ((RubikOBTM.blockPermutation m).symm_apply_apply s)
    obtain ⟨m, hm⟩ := hedge
    refine ⟨m :: w, ?_, ?_⟩
    · simp [hwlen]
    · change RubikOBTM.applyBlockWord w (RubikOBTM.applyBlock m u.val) = z.val
      rw [hm, hw]
