import RubikSTM.Proofs.OBTM.Grouping.GroupOfMonotone
import RubikSTM.Definitions.OBTM.Grouping.GroupOf
set_option autoImplicit false

theorem RubikOBTM.Grouping.groupOf_monotone :
    ∀ (m h : ℕ) (hh : 0 < h), Monotone (RubikOBTM.Grouping.groupOf m h hh) :=
  @proof_RubikOBTM_Grouping_groupOf_monotone
