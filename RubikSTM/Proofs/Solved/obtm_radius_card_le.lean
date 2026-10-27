import RubikSTM.Definitions.Solved.Metrics
import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Lemmas.Solved.obtm_fixedRadius_count
set_option autoImplicit false

theorem proof_RubikSolved_obtm_radius_card_le {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card (Rubik.Position n) ≤
      (18 * n + 1) ^ (RubikSolved.solvedLookingRadius (RubikOBTM.obtmGraph n) + 6) := by
  classical
  have hcover : ∀ p : Rubik.Position n,
      RubikSolved.solvedLookingDistance (RubikOBTM.obtmGraph n) p ≤
        RubikSolved.solvedLookingRadius (RubikOBTM.obtmGraph n) := by
    intro p
    exact Finset.le_sup
      (f := RubikSolved.solvedLookingDistance (RubikOBTM.obtmGraph n)) (Finset.mem_univ p)
  calc
    Fintype.card (Rubik.Position n) ≤ 6 ^ 6 *
        (18 * (n - 1) + 1) ^ RubikSolved.solvedLookingRadius (RubikOBTM.obtmGraph n) :=
      RubikSolved.obtm_fixedRadius_count hn _ hcover
    _ ≤ (18 * n + 1) ^ 6 *
        (18 * n + 1) ^ RubikSolved.solvedLookingRadius (RubikOBTM.obtmGraph n) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) 6)
        (Nat.pow_le_pow_left (by omega) _)
    _ = (18 * n + 1) ^ (RubikSolved.solvedLookingRadius (RubikOBTM.obtmGraph n) + 6) := by
      rw [pow_add, Nat.mul_comm]
