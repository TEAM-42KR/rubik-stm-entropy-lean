import RubikSTM.Proofs.OBTM.Grouping.FibreInterval
import RubikSTM.Definitions.OBTM.Grouping.GroupOf
set_option autoImplicit false

theorem RubikOBTM.Grouping.fibre_interval :
    ∀ (m h : ℕ) (hh : 0 < h) (t : Fin h) (hg : (RubikOBTM.Grouping.group m h hh t).Nonempty), RubikOBTM.Grouping.positiveGroup m h hh t = Finset.Icc (RubikOBTM.Grouping.lower m h hh t hg) (RubikOBTM.Grouping.upper m h hh t hg) ∧ 1 ≤ RubikOBTM.Grouping.lower m h hh t hg ∧ RubikOBTM.Grouping.lower m h hh t hg ≤ RubikOBTM.Grouping.upper m h hh t hg ∧ RubikOBTM.Grouping.upper m h hh t hg ≤ m :=
  @proof_RubikOBTM_Grouping_fibre_interval
