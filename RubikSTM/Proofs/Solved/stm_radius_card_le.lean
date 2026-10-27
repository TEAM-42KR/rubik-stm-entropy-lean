import RubikSTM.Definitions.Solved.Metrics
import RubikSTM.Lemmas.Solved.stm_fixedRadius_count
set_option autoImplicit false

theorem proof_RubikSolved_stm_radius_card_le {n : ℕ} (hn : 2 ≤ n) :
    Fintype.card (Rubik.Position n) ≤
      (9 * n + 1) ^ (RubikSolved.solvedLookingRadius (Rubik.stmGraph n) + 6) := by
  classical
  have hcover : ∀ p : Rubik.Position n,
      RubikSolved.solvedLookingDistance (Rubik.stmGraph n) p ≤
        RubikSolved.solvedLookingRadius (Rubik.stmGraph n) := by
    intro p
    exact Finset.le_sup
      (f := RubikSolved.solvedLookingDistance (Rubik.stmGraph n)) (Finset.mem_univ p)
  calc
    Fintype.card (Rubik.Position n) ≤ 6 ^ 6 *
        (9 * n + 1) ^ RubikSolved.solvedLookingRadius (Rubik.stmGraph n) :=
      RubikSolved.stm_fixedRadius_count n _ hcover
    _ ≤ (9 * n + 1) ^ 6 *
        (9 * n + 1) ^ RubikSolved.solvedLookingRadius (Rubik.stmGraph n) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) 6)
    _ = (9 * n + 1) ^ (RubikSolved.solvedLookingRadius (Rubik.stmGraph n) + 6) := by
      rw [pow_add, Nat.mul_comm]
