import RubikSTM.Proofs.OBTM.Grouping.GroupCardExact
import RubikSTM.Definitions.Grouping.GroupOf
set_option autoImplicit false

theorem RubikGrouping.group_card_exact :
    ∀ (m h : ℕ) (hh : 0 < h) (t : Fin h), (RubikGrouping.group m h hh t).card = m / h + if t.val < m % h then 1 else 0 :=
  @proof_RubikGrouping_group_card_exact
