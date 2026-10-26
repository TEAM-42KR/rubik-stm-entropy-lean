import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Lemmas.OBTM.ObtmGraphConnected
set_option autoImplicit false

theorem proof_RubikOBTM_obtmGraph_ediam_ne_top {n : ℕ} (hn : 2 ≤ n) : (RubikOBTM.obtmGraph n).ediam ≠ ⊤ := by
  letI : Nonempty (Rubik.Position n) := ⟨⟨Rubik.solved n, ⟨[], rfl⟩⟩⟩
  exact (RubikOBTM.obtmGraph n).connected_iff_ediam_ne_top.mp (RubikOBTM.obtmGraph_connected hn)
