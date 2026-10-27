import RubikSTM.Definitions.Solved.Metrics
import RubikSTM.Lemmas.Solved.solvedLookingDistance_attained
import RubikSTM.Lemmas.Solved.solvedLooking_card_le
import RubikSTM.Lemmas.Solved.multiSourceWordCount
import RubikSTM.Lemmas.SolvedSupport.Rubik_stmGraph_connected
import RubikSTM.Definitions.Wings.SolverWord
import RubikSTM.Lemmas.Geometry.ApplyWordAppend
import RubikSTM.Lemmas.SolvedSupport.Rubik_move_card
import RubikSTM.Lemmas.OBTM.OrbitGeometry.G.SumPowersLe
set_option autoImplicit false

private theorem RubikSolved.finite_stm_move_inverse_v12 {n : ℕ} (m : Rubik.Move n) :
    ∃ m' : Rubik.Move n, ∀ c : Rubik.Colouring n,
      Rubik.applyMove m' (Rubik.applyMove m c) = c := by
  let m' : Rubik.Move n := (m.1, m.2.1, m.2.2.rev)
  have hsum : (m.2.2.rev.val + 1) + (m.2.2.val + 1) = 4 := by
    simp only [Fin.val_rev]
    have ht := m.2.2.isLt
    omega
  have hprod : Rubik.movePermutation m' * Rubik.movePermutation m = 1 := by
    change (Rubik.sliceQuarter n m.1 m.2.1) ^ (m.2.2.rev.val + 1) *
      (Rubik.sliceQuarter n m.1 m.2.1) ^ (m.2.2.val + 1) = 1
    rw [← pow_add, hsum, Rubik.sliceQuarter_order_four]
  have hinv : Rubik.movePermutation m' = (Rubik.movePermutation m)⁻¹ :=
    mul_eq_one_iff_eq_inv.mp hprod
  refine ⟨m', ?_⟩
  intro c
  funext s
  change c ((Rubik.movePermutation m).symm ((Rubik.movePermutation m').symm s)) = c s
  rw [hinv]
  exact congrArg c ((Rubik.movePermutation m).symm_apply_apply s)

private theorem RubikSolved.finite_stm_walk_word_v12 {n : ℕ} {u v : Rubik.Position n}
    (p : (Rubik.stmGraph n).Walk u v) :
    ∃ w : List (Rubik.Move n),
      w.length = p.length ∧ Rubik.applyWord w u.val = v.val := by
  induction p with
  | nil => exact ⟨[], rfl, rfl⟩
  | @cons u v z h p ih =>
      obtain ⟨w, hwlen, hw⟩ := ih
      have hedge : ∃ m : Rubik.Move n, Rubik.applyMove m u.val = v.val := by
        rcases h.2 with hf | hr
        · exact hf
        · obtain ⟨m, hm⟩ := hr
          obtain ⟨m', hinv⟩ := RubikSolved.finite_stm_move_inverse_v12 m
          refine ⟨m', ?_⟩
          rw [← hm, hinv]
      obtain ⟨m, hm⟩ := hedge
      refine ⟨m :: w, ?_, ?_⟩
      · simp [hwlen]
      · change Rubik.applyWord w (Rubik.applyMove m u.val) = z.val
        rw [hm, hw]

theorem proof_RubikSolved_stm_fixedRadius_count (n d : ℕ)
    (hcover : ∀ p : Rubik.Position n,
      RubikSolved.solvedLookingDistance (Rubik.stmGraph n) p ≤ d) :
    Fintype.card (Rubik.Position n) ≤ 6 ^ 6 * (9 * n + 1) ^ d := by
  classical
  let Source := {p : Rubik.Position n // RubikSolved.IsSolvedLooking p}
  let run : Source → List (Rubik.Move n) → Rubik.Position n := fun q w =>
    ⟨Rubik.applyWord w q.val.val, by
      obtain ⟨u, hu⟩ := q.val.property
      refine ⟨u ++ w, ?_⟩
      rw [Rubik.applyWord_append, hu]⟩
  have cover : ∀ p : Rubik.Position n, ∃ q : Source, ∃ w : List (Rubik.Move n),
      w.length ≤ d ∧ run q w = p := by
    intro p
    obtain ⟨q, hq, hd⟩ := RubikSolved.solvedLookingDistance_attained (Rubik.stmGraph n) p
    obtain ⟨pw, hpw⟩ := (Rubik.stmGraph_connected n).exists_walk_length_eq_dist q p
    obtain ⟨w, hwl, hw⟩ := RubikSolved.finite_stm_walk_word_v12 pw
    refine ⟨⟨q, hq⟩, w, ?_, ?_⟩
    · calc
        w.length = pw.length := hwl
        _ = (Rubik.stmGraph n).dist q p := hpw
        _ = (Rubik.stmGraph n).dist p q := SimpleGraph.dist_comm
        _ = RubikSolved.solvedLookingDistance (Rubik.stmGraph n) p := hd
        _ ≤ d := hcover p
    · apply Subtype.ext
      exact hw
  have hs : Fintype.card Source ≤ 6 ^ 6 := by
    simpa only [Source, Nat.card_eq_fintype_card] using RubikSolved.solvedLooking_card_le n
  calc
    Fintype.card (Rubik.Position n) ≤ Fintype.card Source *
        ∑ j ∈ Finset.range (d + 1), Fintype.card (Rubik.Move n) ^ j :=
      RubikSolved.multiSourceWordCount run d cover
    _ = Fintype.card Source * ∑ j ∈ Finset.range (d + 1), (9 * n) ^ j := by
      rw [Rubik.move_card]
    _ ≤ 6 ^ 6 * ∑ j ∈ Finset.range (d + 1), (9 * n) ^ j :=
      Nat.mul_le_mul_right _ hs
    _ ≤ 6 ^ 6 * (9 * n + 1) ^ d :=
      Nat.mul_le_mul_left _ (RubikGeometry.G.sum_powers_le (9 * n) d)
