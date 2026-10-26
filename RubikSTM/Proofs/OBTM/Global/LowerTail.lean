import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Lemmas.OBTM.ReachableEntropy
import RubikSTM.Lemmas.OBTM.Global.CardPositionLePow
import RubikSTM.Lemmas.OBTM.Global.CountingLowerLinear
set_option autoImplicit false
open Filter Topology

theorem proof_RubikOBTM_Global_lowerTail (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Rubik.entropyConstant - ε ≤ RubikOBTM.normalizedDiameter n := by
  have hq : 1 ≤ RubikGeometry.orbitColourings := by
    norm_num [RubikGeometry.orbitColourings, Nat.factorial]
  have hqcast : (RubikGeometry.orbitColourings : ℝ) =
      (Nat.factorial 24 : ℝ) / (Nat.factorial 4 : ℝ) ^ 6 := by
    norm_num [RubikGeometry.orbitColourings, Nat.factorial]
  have hcount : ∀ᶠ n : ℕ in Filter.atTop,
      RubikGeometry.orbitColourings ^ ((n - 2) / 2 * ((n - 2) / 2 - 1)) ≤
        (18 * n + 1) ^ RubikOBTM.obtmDiameter n := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    exact (RubikOBTM.ReachableEntropy n).trans
      ((RubikOBTM.Global.card_position_le_pow hn).trans
        (Nat.pow_le_pow_left (by omega) _))
  simpa only [Rubik.entropyConstant, RubikOBTM.normalizedDiameter, hqcast] using
    RubikOBTM.Global.counting_lower_linear RubikGeometry.orbitColourings 18 hq (by norm_num)
      RubikOBTM.obtmDiameter hcount ε hε
