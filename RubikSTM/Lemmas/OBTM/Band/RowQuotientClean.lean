import RubikSTM.Proofs.OBTM.Band.RowQuotientClean
import RubikSTM.Definitions.OBTM.Band.Finite.ModelEval
set_option autoImplicit false

theorem RubikOBTM.Band.row_quotient_clean :
    ∀ {n : ℕ} (a u v : Fin n) (h : RubikOBTM.Band.Admissible n a u v) (σ τ : Equiv.Perm (Fin 24)) (ms ns : List (Rubik.Move n)) (hm : RubikBand.StrictControl a ms) (hn : RubikBand.StrictControl a ns) (hσ : ∀ d : Fin n, RubikOBTM.Band.InInterval u v d → ∀ i : Fin 24, (RubikBand.wordPerm ms (RubikOBTM.Band.plus a d i) = RubikOBTM.Band.plus a d (σ i)) ∧ (RubikBand.wordPerm ms (RubikOBTM.Band.minus a d i) = RubikOBTM.Band.minus a d (σ i))) (hτ : ∀ d : Fin n, RubikOBTM.Band.InInterval u v d → ∀ i : Fin 24, (RubikBand.wordPerm ns (RubikOBTM.Band.plus a d i) = RubikOBTM.Band.plus a d (τ i)) ∧ (RubikBand.wordPerm ns (RubikOBTM.Band.minus a d i) = RubikOBTM.Band.minus a d (τ i))), RubikOBTM.Band.CleanAction a u v (RubikOBTM.Band.Finite.kernel (σ,τ)) ((RubikBand.wordPerm ms * RubikOBTM.Band.slabPerm u v * (RubikBand.wordPerm ms)⁻¹) * (RubikBand.wordPerm ns * RubikOBTM.Band.slabPerm u v * (RubikBand.wordPerm ns)⁻¹)⁻¹) :=
  @proof_RubikOBTM_Band_row_quotient_clean
