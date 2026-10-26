import RubikSTM.Proofs.OBTM.Grouping.DepthGroupInterval
import RubikSTM.Definitions.OBTM.Grouping.GroupOf
set_option autoImplicit false

theorem RubikOBTM.Grouping.depthGroup_interval :
    ∀ (n h : ℕ) (hh : 0 < h) (t : Fin h) (hg : (RubikOBTM.Grouping.group ((n-2)/2) h hh t).Nonempty), RubikOBTM.Grouping.depthGroup n h hh t = Finset.univ.filter (fun d : Fin n => RubikOBTM.Grouping.lower ((n-2)/2) h hh t hg ≤ d.val ∧ d.val ≤ RubikOBTM.Grouping.upper ((n-2)/2) h hh t hg) ∧ 1 ≤ RubikOBTM.Grouping.lower ((n-2)/2) h hh t hg ∧ RubikOBTM.Grouping.lower ((n-2)/2) h hh t hg ≤ RubikOBTM.Grouping.upper ((n-2)/2) h hh t hg ∧ 2 * RubikOBTM.Grouping.upper ((n-2)/2) h hh t hg + 2 ≤ n :=
  @proof_RubikOBTM_Grouping_depthGroup_interval
