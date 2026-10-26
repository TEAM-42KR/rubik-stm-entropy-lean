import RubikSTM.Definitions.Geometry.StmGraph
import RubikSTM.Definitions.WordBounds.CostEnvelope
import RubikSTM.Lemmas.OrbitGeometry.CardNormalTableOrbit
import RubikSTM.Lemmas.Channel.Paired.StateCard
import RubikSTM.Lemmas.Channel.Paired.LogCardDivEight
set_option autoImplicit false

private theorem rlq_q_eq_orbitColourings :
    RubikCostBridge.q = (RubikGeometry.orbitColourings : ℝ) := by
  unfold RubikCostBridge.q
  rw [← Nat.card_eq_fintype_card]
  change ((Nat.card {f : Fin 24 → Rubik.Normal // ∃ σ : Equiv.Perm (Fin 24),
    f = RubikGeometry.normalTable ∘ σ} : ℕ) : ℝ) = (RubikGeometry.orbitColourings : ℝ)
  rw [RubikGeometry.card_normalTable_orbit]

theorem proof_RubikAsymptotics_costBridge_q_identity : Real.log RubikCostBridge.q / 4 = Rubik.entropyConstant := by
  rw [← RubikChannel.Paired.log_card_div_eight, RubikChannel.Paired.StateCard,
    rlq_q_eq_orbitColourings, Nat.cast_pow, Real.log_pow]
  push_cast
  ring
