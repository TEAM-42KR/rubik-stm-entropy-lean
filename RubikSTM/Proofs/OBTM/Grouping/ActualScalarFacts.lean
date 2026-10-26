import RubikSTM.Definitions.OBTM.Grouping.GroupOf
import RubikSTM.Lemmas.OBTM.Grouping.DepthGroupLink
import RubikSTM.Lemmas.OBTM.Grouping.SamePairsCardEq
import RubikSTM.Lemmas.OBTM.Grouping.GroupCardExact
import RubikSTM.Lemmas.OBTM.Grouping.SameGroupPairsBound
import RubikSTM.Lemmas.OBTM.Grouping.CrossGroupProductsBound
set_option autoImplicit false

theorem proof_RubikOBTM_Grouping_actual_scalar_facts (n h : ℕ) (hh : 0 < h) :
    let m := (n-2)/2
    let f := RubikOBTM.Grouping.groupOf m h hh
    (∀ t : Fin h, m / h ≤ (RubikGlobalWord.depthGroup f t).card ∧
      (RubikGlobalWord.depthGroup f t).card ≤ m / h + 1) ∧
    (∑ s : Fin h, ∑ t : Fin h, if s < t then
      ((RubikGlobalWord.depthGroup f s).card : ℝ) * (RubikGlobalWord.depthGroup f t).card else 0) ≤ (m : ℝ)^2 / 2 ∧
    (RubikGlobalWord.sameCount f : ℝ) ≤ (m : ℝ)^2 / h + m := by
  classical
  dsimp only
  let m := (n-2)/2
  let f := RubikOBTM.Grouping.groupOf m h hh
  have hc (t : Fin h) : (RubikGlobalWord.depthGroup f t).card = (RubikGrouping.group m h hh t).card := by
    rw [← (RubikOBTM.Grouping.depthGroup_link n h hh t).1]
    exact (RubikOBTM.Grouping.depthGroup_link n h hh t).2
  have hsame : RubikGlobalWord.sameCount f = (RubikOBTM.Grouping.sameGroupPairs m h hh).card := by
    let S := RubikOBTM.Grouping.sameGroupPairs m h hh
    let e : RubikGlobalWord.SamePair f ≃ S :=
      { toFun := fun p => ⟨p.val.val, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, p.val.property, p.property⟩⟩
        invFun := fun p => ⟨⟨p.val, (Finset.mem_filter.mp p.property).2.1⟩,
          (Finset.mem_filter.mp p.property).2.2⟩
        left_inv := by intro p; rfl
        right_inv := by intro p; rfl }
    exact (Fintype.card_congr e).trans (Fintype.card_coe S)
  refine ⟨?_, ?_, ?_⟩
  · intro t
    change m / h ≤ (RubikGlobalWord.depthGroup f t).card ∧
      (RubikGlobalWord.depthGroup f t).card ≤ m / h + 1
    rw [hc, RubikGrouping.group_card_exact]
    split_ifs <;> omega
  · have he : (∑ s : Fin h, ∑ t : Fin h, if s < t then
        ((RubikGlobalWord.depthGroup f s).card : ℝ) * (RubikGlobalWord.depthGroup f t).card else 0) =
        RubikGrouping.crossGroupProducts m h hh := by
      simp only [hc, RubikGrouping.crossGroupProducts, Finset.sum_filter]
    rw [he]
    exact RubikGrouping.cross_group_products_bound m h hh
  · rw [hsame, RubikOBTM.Grouping.same_pairs_card_eq]
    exact RubikGrouping.same_group_pairs_bound m h hh
