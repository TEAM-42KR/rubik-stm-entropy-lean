import RubikSTM.Definitions.Grouping.GroupOf
set_option autoImplicit false

private theorem RubikGrouping.mem_group_iff (m h : ℕ) (hh : 0 < h)
    (t : Fin h) (i : Fin m) :
    i ∈ RubikGrouping.group m h hh t ↔ RubikGrouping.groupOf m h hh i = t := by
  simp only [RubikGrouping.group, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem RubikGrouping.groups_cover (m h : ℕ) (hh : 0 < h) :
    Finset.univ.biUnion (RubikGrouping.group m h hh) = Finset.univ := by
  ext i
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, RubikGrouping.mem_group_iff]
  exact ⟨fun _ => trivial, fun _ => ⟨RubikGrouping.groupOf m h hh i, rfl⟩⟩

private theorem RubikGrouping.groups_disjoint (m h : ℕ) (hh : 0 < h)
    (s t : Fin h) (hst : s ≠ t) :
    Disjoint (RubikGrouping.group m h hh s) (RubikGrouping.group m h hh t) := by
  apply Finset.disjoint_left.mpr
  intro i his hit
  exact hst (((RubikGrouping.mem_group_iff m h hh s i).mp his).symm.trans
    ((RubikGrouping.mem_group_iff m h hh t i).mp hit))

private theorem RubikGrouping.group_card_exact (m h : ℕ) (hh : 0 < h) (t : Fin h) :
    (RubikGrouping.group m h hh t).card = m / h + if t.val < m % h then 1 else 0 := by
  have he : (RubikGrouping.group m h hh t).card =
      Nat.count (fun x => x ≡ t.val [MOD h]) m := by
    rw [Nat.count_eq_card_filter_range]
    simp only [RubikGrouping.group, Finset.card_filter, RubikGrouping.groupOf, Fin.ext_iff]
    change (∑ i : Fin m, if i.val % h = t.val then (1 : ℕ) else 0) = _
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i % h = t.val then (1 : ℕ) else 0) m]
    simp only [Nat.ModEq, Nat.mod_eq_of_lt t.isLt]
  rw [he, Nat.count_modEq_card m hh t.val, Nat.mod_eq_of_lt t.isLt]

private theorem RubikGrouping.group_card_floor_or_ceil (m h : ℕ) (hh : 0 < h) (t : Fin h) :
    (RubikGrouping.group m h hh t).card = m / h ∨
      (RubikGrouping.group m h hh t).card = (m + h - 1) / h := by
  rw [RubikGrouping.group_card_exact]
  split_ifs with ht
  · right
    have hr : 0 < m % h := lt_of_le_of_lt (Nat.zero_le t.val) ht
    have hrem := Nat.mod_lt m hh
    have hdiv := Nat.div_add_mod m h
    have hsub : m + h - 1 + 1 = m + h := by omega
    symm
    apply Nat.div_eq_of_lt_le
    · nlinarith only [hdiv, hsub, hr]
    · nlinarith only [hdiv, hsub, hrem]
  · exact Or.inl (by omega)

private theorem RubikGrouping.sum_group_card (m h : ℕ) (hh : 0 < h) :
    ∑ t : Fin h, (RubikGrouping.group m h hh t).card = m := by
  have hf := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin m))
    (Finset.univ : Finset (Fin h)) (RubikGrouping.groupOf m h hh)
  simpa only [RubikGrouping.group, Finset.mem_univ, Finset.filter_true, Finset.card_univ,
    Fintype.card_fin] using hf

private theorem RubikGrouping.group_card_real_le (m h : ℕ) (hh : 0 < h) (t : Fin h) :
    ((RubikGrouping.group m h hh t).card : ℝ) ≤ (m : ℝ) / (h : ℝ) + 1 := by
  have hd : ((m / h : ℕ) : ℝ) ≤ (m : ℝ) / (h : ℝ) := Nat.cast_div_le
  rw [RubikGrouping.group_card_exact]
  split_ifs <;> push_cast <;> linarith only [hd]

private theorem RubikGrouping.same_group_pairs_bound (m h : ℕ) (hh : 0 < h) :
    ((RubikGrouping.sameGroupPairs m h hh).card : ℝ) ≤
      (m : ℝ) ^ 2 / (h : ℝ) + (m : ℝ) := by
  have hcount : (RubikGrouping.sameGroupPairs m h hh).card ≤
      ∑ i : Fin m, (RubikGrouping.group m h hh (RubikGrouping.groupOf m h hh i)).card := by
    unfold RubikGrouping.sameGroupPairs
    rw [Finset.card_filter, Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro i _
    rw [RubikGrouping.group, Finset.card_filter]
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : i ≠ j ∧ RubikGrouping.groupOf m h hh i = RubikGrouping.groupOf m h hh j
    · rw [if_pos hij, if_pos hij.2.symm]
    · simp only [hij, if_false]
      positivity
  have hreal : ((RubikGrouping.sameGroupPairs m h hh).card : ℝ) ≤
      ∑ i : Fin m, ((RubikGrouping.group m h hh (RubikGrouping.groupOf m h hh i)).card : ℝ) := by
    exact_mod_cast hcount
  calc
    ((RubikGrouping.sameGroupPairs m h hh).card : ℝ) ≤
        ∑ i : Fin m, ((RubikGrouping.group m h hh (RubikGrouping.groupOf m h hh i)).card : ℝ) := hreal
    _ ≤ ∑ _i : Fin m, ((m : ℝ) / (h : ℝ) + 1) :=
      Finset.sum_le_sum (fun i _ => RubikGrouping.group_card_real_le m h hh _)
    _ = (m : ℝ) ^ 2 / (h : ℝ) + (m : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem proof_RubikGrouping_cross_group_products_bound (m h : ℕ) (hh : 0 < h) :
    RubikGrouping.crossGroupProducts m h hh ≤ (m : ℝ) ^ 2 / 2 := by
  let a : Fin h → ℝ := fun t => (RubikGrouping.group m h hh t).card
  have ha (t : Fin h) : 0 ≤ a t := Nat.cast_nonneg _
  have hsum : ∑ t : Fin h, a t = (m : ℝ) := by
    dsimp [a]
    exact_mod_cast RubikGrouping.sum_group_card m h hh
  let U : ℝ := ∑ s : Fin h, ∑ t ∈ Finset.univ.filter (fun t : Fin h => s < t), a s * a t
  let V : ℝ := ∑ s : Fin h, ∑ t ∈ Finset.univ.filter (fun t : Fin h => t < s), a s * a t
  have hswap : V = U := by
    dsimp [V, U]
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> ring
  have hle : U + V ≤ (m : ℝ) ^ 2 := by
    have htotal : (∑ s : Fin h, ∑ t : Fin h, a s * a t) = (m : ℝ) ^ 2 := by
      rw [← Finset.sum_mul_sum, hsum]
      ring
    rw [← htotal]
    dsimp [U, V]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro s _
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t _
    by_cases hst : s < t
    · have hts : ¬ t < s := not_lt.mpr hst.le
      simp only [hst, hts, if_true, if_false, add_zero, le_refl]
    · by_cases hts : t < s
      · simp only [hst, hts, if_true, if_false, zero_add, le_refl]
      · simp only [hst, hts, if_false, zero_add]
        exact mul_nonneg (ha _) (ha _)
  change U ≤ (m : ℝ) ^ 2 / 2
  rw [hswap] at hle
  linarith only [hle]
