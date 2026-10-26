import RubikSTM.Definitions.WordBounds.CostEnvelope
set_option autoImplicit false

open RubikCostBridge

theorem proof_RubikCostBridge_rowCeil_eq_natCeil (r k : ℕ) (hk : 0 < k) :
    RubikRectangle.rowCeil r k = ⌈(r : ℝ) / (k : ℝ)⌉₊ := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hcR := (div_le_iff₀ hkR).mp (Nat.le_ceil ((r : ℝ)/(k : ℝ)))
  have hc : r ≤ ⌈(r : ℝ)/(k : ℝ)⌉₊ * k := by exact_mod_cast hcR
  apply Nat.le_antisymm
  · apply (Nat.div_le_iff_le_mul_add_pred hk).mpr
    rw [show r+k-1=r+(k-1) by omega, mul_comm k]
    exact Nat.add_le_add_right hc _
  · apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hkR).mpr
    change (r : ℝ) ≤ (((r+k-1)/k : ℕ) : ℝ) * k
    have ht : (r+k-1) < ((r+k-1)/k+1)*k :=
      (Nat.div_lt_iff_lt_mul hk).mp (Nat.lt_succ_self _)
    have he : r+k-1+1 = r+k := by omega
    have hle : r ≤ ((r+k-1)/k)*k := by nlinarith
    exact_mod_cast hle
