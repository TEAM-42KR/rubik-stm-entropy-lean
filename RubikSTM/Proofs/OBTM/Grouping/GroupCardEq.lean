import RubikSTM.Definitions.OBTM.Grouping.GroupOf
set_option autoImplicit false

theorem proof_RubikOBTM_Grouping_group_card_eq (m h : ℕ) (hh : 0 < h) (t : Fin h) :
    (RubikOBTM.Grouping.group m h hh t).card = (RubikGrouping.group m h hh t).card := by
  classical
  apply Finset.card_bij (fun i _ => RubikOBTM.Grouping.sortIndex m h hh i)
  · intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact (Finset.mem_filter.mp hi).2
  · intro i hi j hj he
    exact (RubikOBTM.Grouping.sortIndex m h hh).injective he
  · intro j hj
    refine ⟨(RubikOBTM.Grouping.sortIndex m h hh).symm j, ?_, by simp⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change RubikGrouping.groupOf m h hh ((RubikOBTM.Grouping.sortIndex m h hh)
      ((RubikOBTM.Grouping.sortIndex m h hh).symm j)) = t
    rw [Equiv.apply_symm_apply]
    exact (Finset.mem_filter.mp hj).2
