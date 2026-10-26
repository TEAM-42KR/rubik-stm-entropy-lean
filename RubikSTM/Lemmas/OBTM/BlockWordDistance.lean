import RubikSTM.Proofs.OBTM.BlockWordDistance
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikOBTM.blockWord_distance :
    ∀ {n : ℕ} (w : List (RubikOBTM.BlockMove n)) (u v : Rubik.Position n) (h : RubikOBTM.applyBlockWord w u.val = v.val), (RubikOBTM.obtmGraph n).dist u v ≤ w.length :=
  @proof_RubikOBTM_blockWord_distance
