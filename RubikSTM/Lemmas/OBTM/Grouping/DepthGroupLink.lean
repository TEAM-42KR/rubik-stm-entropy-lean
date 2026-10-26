import RubikSTM.Proofs.OBTM.Grouping.DepthGroupLink
import RubikSTM.Definitions.OBTM.Grouping.GroupOf
set_option autoImplicit false

theorem RubikOBTM.Grouping.depthGroup_link :
    ∀ (n h : ℕ) (hh : 0 < h) (t : Fin h), RubikOBTM.Grouping.depthGroup n h hh t = RubikGlobalWord.depthGroup (RubikOBTM.Grouping.groupOf ((n-2)/2) h hh) t ∧ (RubikOBTM.Grouping.depthGroup n h hh t).card = (RubikGrouping.group ((n-2)/2) h hh t).card :=
  @proof_RubikOBTM_Grouping_depthGroup_link
