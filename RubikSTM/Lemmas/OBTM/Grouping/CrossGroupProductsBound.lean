import RubikSTM.Proofs.OBTM.Grouping.CrossGroupProductsBound
import RubikSTM.Definitions.Grouping.GroupOf
set_option autoImplicit false

theorem RubikGrouping.cross_group_products_bound :
    ∀ (m h : ℕ) (hh : 0 < h), RubikGrouping.crossGroupProducts m h hh ≤ (m : ℝ) ^ 2 / 2 :=
  @proof_RubikGrouping_cross_group_products_bound
