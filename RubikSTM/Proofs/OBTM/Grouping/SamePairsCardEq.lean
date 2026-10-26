import RubikSTM.Definitions.OBTM.Grouping.GroupOf
set_option autoImplicit false

theorem proof_RubikOBTM_Grouping_same_pairs_card_eq (m h : ℕ) (hh : 0 < h) :
    (RubikOBTM.Grouping.sameGroupPairs m h hh).card = (RubikGrouping.sameGroupPairs m h hh).card := by
  classical
  let σ := RubikOBTM.Grouping.sortIndex m h hh
  apply Finset.card_bij (fun p _ => (σ p.1, σ p.2))
  · intro p hp
    obtain ⟨hne, he⟩ := (Finset.mem_filter.mp hp).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, fun h => hne (σ.injective h), he⟩
  · intro p hp q hq he
    apply Prod.ext
    · have h₁ : σ p.1 = σ q.1 := congrArg (fun z : Fin m × Fin m => z.1) he
      exact σ.injective h₁
    · have h₂ : σ p.2 = σ q.2 := congrArg (fun z : Fin m × Fin m => z.2) he
      exact σ.injective h₂
  · intro q hq
    obtain ⟨hne, he⟩ := (Finset.mem_filter.mp hq).2
    refine ⟨(σ.symm q.1, σ.symm q.2), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · exact fun h => hne (σ.symm.injective h)
      · change RubikGrouping.groupOf m h hh (σ (σ.symm q.1)) =
          RubikGrouping.groupOf m h hh (σ (σ.symm q.2))
        simpa using he
    · simp
