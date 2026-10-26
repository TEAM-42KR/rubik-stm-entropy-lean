import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Lemmas.OBTM.BlockWordReachable
import RubikSTM.Lemmas.OBTM.SliceWordToBlocks
set_option autoImplicit false

theorem proof_RubikOBTM_reachable_iff {n : ℕ} (hn : 2 ≤ n) (c : Rubik.Colouring n) :
    RubikOBTM.BlockReachable c ↔ Rubik.Reachable c := by
  constructor
  · rintro ⟨w, hw⟩
    rw [← hw]
    exact RubikOBTM.blockWord_reachable w (Rubik.solved n) ⟨[], rfl⟩
  · rintro ⟨w, hw⟩
    obtain ⟨v, hv, he⟩ := RubikOBTM.sliceWord_to_blocks hn w
    exact ⟨v, (he (Rubik.solved n)).trans hw⟩
