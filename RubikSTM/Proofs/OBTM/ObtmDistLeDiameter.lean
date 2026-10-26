import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Lemmas.OBTM.ObtmGraphEdiamNeTop
set_option autoImplicit false

theorem proof_RubikOBTM_obtm_dist_le_diameter {n : ℕ} (hn : 2 ≤ n) (u v : Rubik.Position n) :
    (RubikOBTM.obtmGraph n).dist u v ≤ RubikOBTM.obtmDiameter n := by
  exact (RubikOBTM.obtmGraph n).dist_le_diam (RubikOBTM.obtmGraph_ediam_ne_top hn)
