import RubikSTM.Proofs.OBTM.Grouping.GroupCardEq
import RubikSTM.Definitions.OBTM.Grouping.GroupOf
set_option autoImplicit false

theorem RubikOBTM.Grouping.group_card_eq :
    ∀ (m h : ℕ) (hh : 0 < h) (t : Fin h), (RubikOBTM.Grouping.group m h hh t).card = (RubikGrouping.group m h hh t).card :=
  @proof_RubikOBTM_Grouping_group_card_eq
