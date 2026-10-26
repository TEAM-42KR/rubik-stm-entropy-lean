import RubikSTM.Proofs.OBTM.Grouping.ActualScalarFacts
import RubikSTM.Definitions.OBTM.Grouping.GroupOf
set_option autoImplicit false

theorem RubikOBTM.Grouping.actual_scalar_facts :
    ∀ (n h : ℕ) (hh : 0 < h),
    let m := (n-2)/2; let f := RubikOBTM.Grouping.groupOf m h hh; (∀ t : Fin h, m / h ≤ (RubikGlobalWord.depthGroup f t).card ∧ (RubikGlobalWord.depthGroup f t).card ≤ m / h + 1) ∧ (∑ s : Fin h, ∑ t : Fin h, if s < t then ((RubikGlobalWord.depthGroup f s).card : ℝ) * (RubikGlobalWord.depthGroup f t).card else 0) ≤ (m : ℝ)^2 / 2 ∧ (RubikGlobalWord.sameCount f : ℝ) ≤ (m : ℝ)^2 / h + m :=
  @proof_RubikOBTM_Grouping_actual_scalar_facts
