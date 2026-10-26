import RubikSTM.Definitions.GlobalWords.Region
import RubikSTM.Lemmas.OBTM.GlobalWords.SumGroupPairs
set_option autoImplicit false

theorem proof_RubikOBTM_Global_dependent_sum_group_pairs {A : Type*} [AddCommMonoid A] (H : ℕ)
    (F : RubikGlobalWord.GroupPair H → A) :
    (∑ p, F p) = ∑ i : Fin H, ∑ j : Fin H,
      if hij : i < j then F ⟨(i,j),hij⟩ else 0 := by
  classical
  let g (i j : Fin H) : A := if hij : i < j then F ⟨(i,j),hij⟩ else 0
  calc
    (∑ p, F p) = ∑ p : RubikGlobalWord.GroupPair H, g p.val.1 p.val.2 := by
      apply Finset.sum_congr rfl
      intro p _
      simp only [g, dif_pos p.property]
    _ = ∑ i : Fin H, ∑ j : Fin H, if i < j then g i j else 0 :=
      RubikGlobalWord.sum_group_pairs g
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i < j <;> simp [g,hij]
