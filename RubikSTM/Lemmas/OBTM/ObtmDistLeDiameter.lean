import RubikSTM.Proofs.OBTM.ObtmDistLeDiameter
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikOBTM.obtm_dist_le_diameter :
    ∀ {n : ℕ} (hn : 2 ≤ n) (u v : Rubik.Position n), (RubikOBTM.obtmGraph n).dist u v ≤ RubikOBTM.obtmDiameter n :=
  @proof_RubikOBTM_obtm_dist_le_diameter
