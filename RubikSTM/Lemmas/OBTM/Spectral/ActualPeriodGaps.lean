import RubikSTM.Proofs.OBTM.Spectral.ActualPeriodGaps
import RubikSTM.Definitions.OBTM.Spectral.ActualPeriodPositive
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator

theorem RubikOBTM.Spectral.actual_period_gaps :
    ∃ θ η : ℝ, 0 < θ ∧ θ < 1 ∧ 0 < η ∧ η < 1 ∧ (∀ n : Fin RubikOBTM.Finite.period → RubikOBTM.Finite.Intrinsic, ‖RubikOBTM.Spectral.singleWordMatrix RubikOBTM.Spectral.actualPeriodPositive RubikOBTM.Finite.nativeC RubikOBTM.Spectral.actualAlphabetNonempty RubikOBTM.Finite.periodicAct n - RubikOBTM.Spectral.averaging‖ ≤ θ) ∧ (∀ (n : Fin RubikOBTM.Finite.period → RubikOBTM.Finite.Intrinsic) (shared : Fin RubikOBTM.Finite.period → Bool), (∃ i, shared i = false) → ‖RubikOBTM.Spectral.doubleWordMatrix RubikOBTM.Spectral.actualPeriodPositive RubikOBTM.Finite.nativeC RubikOBTM.Spectral.actualAlphabetNonempty RubikOBTM.Finite.periodicAct n shared - RubikOBTM.Spectral.averaging‖ ≤ η) :=
  @proof_RubikOBTM_Spectral_actual_period_gaps
