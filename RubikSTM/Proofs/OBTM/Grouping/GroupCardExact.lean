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

theorem proof_RubikGrouping_group_card_exact (m h : ℕ) (hh : 0 < h) (t : Fin h) :
    (RubikGrouping.group m h hh t).card = m / h + if t.val < m % h then 1 else 0 := by
  have he : (RubikGrouping.group m h hh t).card =
      Nat.count (fun x => x ≡ t.val [MOD h]) m := by
    rw [Nat.count_eq_card_filter_range]
    simp only [RubikGrouping.group, Finset.card_filter, RubikGrouping.groupOf, Fin.ext_iff]
    change (∑ i : Fin m, if i.val % h = t.val then (1 : ℕ) else 0) = _
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => if i % h = t.val then (1 : ℕ) else 0) m]
    simp only [Nat.ModEq, Nat.mod_eq_of_lt t.isLt]
  rw [he, Nat.count_modEq_card m hh t.val, Nat.mod_eq_of_lt t.isLt]
