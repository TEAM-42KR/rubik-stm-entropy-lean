import RubikSTM.Proofs.OBTM.BlockWordWalk
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikOBTM.blockWord_walk :
    ∀ {n : ℕ} (w : List (RubikOBTM.BlockMove n)) (u v : Rubik.Position n) (h : RubikOBTM.applyBlockWord w u.val = v.val), ∃ p : (RubikOBTM.obtmGraph n).Walk u v, p.length ≤ w.length :=
  @proof_RubikOBTM_blockWord_walk
