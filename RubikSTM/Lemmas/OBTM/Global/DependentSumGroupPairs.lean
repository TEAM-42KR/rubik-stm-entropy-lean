import RubikSTM.Proofs.OBTM.Global.DependentSumGroupPairs
import RubikSTM.Definitions.GlobalWords.Region
set_option autoImplicit false

theorem RubikOBTM.Global.dependent_sum_group_pairs :
    ∀ {A : Type*} [AddCommMonoid A] (H : ℕ) (F : RubikGlobalWord.GroupPair H → A), (∑ p, F p) = ∑ i : Fin H, ∑ j : Fin H, if hij : i < j then F ⟨(i,j),hij⟩ else 0 :=
  @proof_RubikOBTM_Global_dependent_sum_group_pairs
