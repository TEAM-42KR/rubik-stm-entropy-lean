import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Lemmas.OBTM.BlockWordWalk
set_option autoImplicit false

theorem proof_RubikOBTM_blockWord_distance {n : ℕ} (w : List (RubikOBTM.BlockMove n)) (u v : Rubik.Position n)
    (h : RubikOBTM.applyBlockWord w u.val = v.val) :
    (RubikOBTM.obtmGraph n).dist u v ≤ w.length := by
  obtain ⟨p, hp⟩ := RubikOBTM.blockWord_walk w u v h
  exact (SimpleGraph.dist_le p).trans hp
