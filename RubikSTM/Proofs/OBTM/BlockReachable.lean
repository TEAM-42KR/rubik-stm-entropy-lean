import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Lemmas.OBTM.BlockSliceWordAction
import RubikSTM.Lemmas.Geometry.ApplyWordAppend
set_option autoImplicit false

theorem proof_RubikOBTM_block_reachable {n : ℕ} (m : RubikOBTM.BlockMove n) (c : Rubik.Colouring n)
    (hc : Rubik.Reachable c) : Rubik.Reachable (RubikOBTM.applyBlock m c) := by
  obtain ⟨w, hw⟩ := hc
  refine ⟨w ++ RubikOBTM.blockSliceWord m, ?_⟩
  rw [Rubik.applyWord_append, hw, RubikOBTM.blockSliceWord_action]
