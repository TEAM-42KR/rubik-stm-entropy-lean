import RubikSTM.Definitions.Solved.Metrics
import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Lemmas.Solved.solvedLookingDistance_attained
import RubikSTM.Lemmas.Solved.solvedLooking_card_le
import RubikSTM.Lemmas.Solved.multiSourceWordCount
import RubikSTM.Lemmas.OBTM.ObtmGraphConnected
import RubikSTM.Lemmas.OBTM.ObtmGraphWalkWord
import RubikSTM.Lemmas.OBTM.BlockWordReachable
import RubikSTM.Lemmas.OBTM.BlockMoveCard
import RubikSTM.Lemmas.OBTM.OrbitGeometry.G.SumPowersLe
set_option autoImplicit false

theorem proof_RubikSolved_obtm_fixedRadius_count {n : ℕ} (hn : 2 ≤ n) (d : ℕ)
    (hcover : ∀ p : Rubik.Position n,
      RubikSolved.solvedLookingDistance (RubikOBTM.obtmGraph n) p ≤ d) :
    Fintype.card (Rubik.Position n) ≤ 6 ^ 6 * (18 * (n - 1) + 1) ^ d := by
  classical
  let Source := {p : Rubik.Position n // RubikSolved.IsSolvedLooking p}
  let run : Source → List (RubikOBTM.BlockMove n) → Rubik.Position n := fun q w =>
    ⟨RubikOBTM.applyBlockWord w q.val.val, RubikOBTM.blockWord_reachable w q.val.val q.val.property⟩
  have cover : ∀ p : Rubik.Position n, ∃ q : Source, ∃ w : List (RubikOBTM.BlockMove n),
      w.length ≤ d ∧ run q w = p := by
    intro p
    obtain ⟨q, hq, hd⟩ := RubikSolved.solvedLookingDistance_attained (RubikOBTM.obtmGraph n) p
    obtain ⟨pw, hpw⟩ := (RubikOBTM.obtmGraph_connected hn).exists_walk_length_eq_dist q p
    obtain ⟨w, hwl, hw⟩ := RubikOBTM.obtmGraph_walk_word pw
    refine ⟨⟨q, hq⟩, w, ?_, ?_⟩
    · calc
        w.length = pw.length := hwl
        _ = (RubikOBTM.obtmGraph n).dist q p := hpw
        _ = (RubikOBTM.obtmGraph n).dist p q := SimpleGraph.dist_comm
        _ = RubikSolved.solvedLookingDistance (RubikOBTM.obtmGraph n) p := hd
        _ ≤ d := hcover p
    · apply Subtype.ext
      exact hw
  have hs : Fintype.card Source ≤ 6 ^ 6 := by
    simpa only [Source, Nat.card_eq_fintype_card] using RubikSolved.solvedLooking_card_le n
  calc
    Fintype.card (Rubik.Position n) ≤ Fintype.card Source *
        ∑ j ∈ Finset.range (d + 1), Fintype.card (RubikOBTM.BlockMove n) ^ j :=
      RubikSolved.multiSourceWordCount run d cover
    _ = Fintype.card Source * ∑ j ∈ Finset.range (d + 1), (18 * (n - 1)) ^ j := by
      rw [RubikOBTM.blockMove_card]
    _ ≤ 6 ^ 6 * ∑ j ∈ Finset.range (d + 1), (18 * (n - 1)) ^ j :=
      Nat.mul_le_mul_right _ hs
    _ ≤ 6 ^ 6 * (18 * (n - 1) + 1) ^ d :=
      Nat.mul_le_mul_left _ (RubikGeometry.G.sum_powers_le (18 * (n - 1)) d)
