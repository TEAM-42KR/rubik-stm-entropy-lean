import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Lemmas.OBTM.ObtmGraphConnected
import RubikSTM.Lemmas.OBTM.ObtmDistLeDiameter
import RubikSTM.Lemmas.OBTM.ObtmGraphWalkWord
set_option autoImplicit false

theorem proof_RubikOBTM_diameter_word_cover {n : ℕ} (hn : 2 ≤ n) (v : Rubik.Position n) :
    ∃ w : List (RubikOBTM.BlockMove n), w.length ≤ RubikOBTM.obtmDiameter n ∧
      RubikOBTM.applyBlockWord w (Rubik.solved n) = v.val := by
  let start : Rubik.Position n := ⟨Rubik.solved n, ⟨[], rfl⟩⟩
  obtain ⟨p, hp⟩ := (RubikOBTM.obtmGraph_connected hn).exists_walk_length_eq_dist start v
  obtain ⟨w, hwlen, hw⟩ := RubikOBTM.obtmGraph_walk_word p
  refine ⟨w, ?_, hw⟩
  calc
    w.length = p.length := hwlen
    _ = (RubikOBTM.obtmGraph n).dist start v := hp
    _ ≤ RubikOBTM.obtmDiameter n := RubikOBTM.obtm_dist_le_diameter hn start v
