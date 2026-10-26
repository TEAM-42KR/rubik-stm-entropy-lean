import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Lemmas.OBTM.Global.CardPositionLeSum
import RubikSTM.Lemmas.OBTM.OrbitGeometry.G.SumPowersLe
set_option autoImplicit false

theorem proof_RubikOBTM_Global_card_position_le_pow {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card (Rubik.Position n) ≤
      (18 * (n - 1) + 1) ^ RubikOBTM.obtmDiameter n :=
  (RubikOBTM.Global.card_position_le_sum hn).trans
    (RubikGeometry.G.sum_powers_le (18 * (n - 1)) (RubikOBTM.obtmDiameter n))
