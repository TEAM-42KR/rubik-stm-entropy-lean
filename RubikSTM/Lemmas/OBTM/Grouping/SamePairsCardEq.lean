import RubikSTM.Proofs.OBTM.Grouping.SamePairsCardEq
import RubikSTM.Definitions.OBTM.Grouping.GroupOf
set_option autoImplicit false

theorem RubikOBTM.Grouping.same_pairs_card_eq :
    ∀ (m h : ℕ) (hh : 0 < h), (RubikOBTM.Grouping.sameGroupPairs m h hh).card = (RubikGrouping.sameGroupPairs m h hh).card :=
  @proof_RubikOBTM_Grouping_same_pairs_card_eq
