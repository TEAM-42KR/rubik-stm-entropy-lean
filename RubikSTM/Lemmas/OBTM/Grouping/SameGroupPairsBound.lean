import RubikSTM.Proofs.OBTM.Grouping.SameGroupPairsBound
import RubikSTM.Definitions.Grouping.GroupOf
set_option autoImplicit false

theorem RubikGrouping.same_group_pairs_bound :
    ∀ (m h : ℕ) (hh : 0 < h), ((RubikGrouping.sameGroupPairs m h hh).card : ℝ) ≤ (m : ℝ) ^ 2 / (h : ℝ) + (m : ℝ) :=
  @proof_RubikGrouping_same_group_pairs_bound
