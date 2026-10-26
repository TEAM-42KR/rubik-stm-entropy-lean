import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Lemmas.OBTM.ReachableIff
import RubikSTM.Lemmas.OBTM.BlockWordWalk
set_option autoImplicit false

theorem proof_RubikOBTM_obtmGraph_connected {n : ℕ} (hn : 2 ≤ n) : (RubikOBTM.obtmGraph n).Connected := by
  let z : Rubik.Position n := ⟨Rubik.solved n, ⟨[], rfl⟩⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable (RubikOBTM.obtmGraph n)).mpr
  refine ⟨z, ?_⟩
  intro c
  obtain ⟨w, hw⟩ := (RubikOBTM.reachable_iff hn c.val).mpr c.property
  obtain ⟨p, hp⟩ := RubikOBTM.blockWord_walk w z c hw
  exact ⟨p⟩
