import RubikSTM.Proofs.OBTM.Spectral.CoordinateBoundsOfPeriodGaps
import RubikSTM.Definitions.OBTM.Spectral.SingleWordMatrix
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator

theorem RubikOBTM.Spectral.coordinate_bounds_of_period_gaps :
    ∀ {T : ℕ} {K Z : Type*} [Group K] [Fintype Z] [DecidableEq Z] [Nonempty Z] (hT : 0 < T) (C : Finset K) (hC : C.Nonempty) (act : Fin T → K →* Equiv.Perm Z) (θ η : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hη0 : 0 < η) (hη1 : η < 1) (hsingle : ∀ n : Fin T → K, ‖RubikOBTM.Spectral.singleWordMatrix hT C hC act n - RubikOBTM.Spectral.averaging‖ ≤ θ) (hdouble : ∀ (n : Fin T → K) (shared : Fin T → Bool), (∃ i, shared i = false) → ‖RubikOBTM.Spectral.doubleWordMatrix hT C hC act n shared - RubikOBTM.Spectral.averaging‖ ≤ η), ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ RubikOBTM.Periodic.CoordinateBounds hT C hC act θ ρ :=
  @proof_RubikOBTM_Spectral_coordinate_bounds_of_period_gaps
