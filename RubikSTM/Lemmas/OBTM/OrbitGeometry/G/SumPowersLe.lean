import RubikSTM.Proofs.OBTM.OrbitGeometry.G.SumPowersLe
import Mathlib
set_option autoImplicit false

theorem RubikGeometry.G.sum_powers_le :
    ∀ (a d : ℕ), (∑ j ∈ Finset.range (d + 1), a ^ j) ≤ (a + 1) ^ d :=
  @proof_RubikGeometry_G_sum_powers_le
