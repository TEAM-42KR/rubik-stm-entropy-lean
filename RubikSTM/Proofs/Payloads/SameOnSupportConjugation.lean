import Mathlib
import RubikSTM.Definitions.Channel.DisjointFourCycleAlphabet
import RubikSTM.Definitions.Orbits.SwapPhi
set_option autoImplicit false

theorem proof_RubikPayload_sameOnSupportConjugation {V : Type*} [Fintype V] [DecidableEq V]
  (f c σ : Equiv.Perm V) (h : ∀ x ∈ f.support, σ x = c x) :
  σ * f * σ⁻¹ = c * f * c⁻¹ := by
  have hd : Equiv.Perm.Disjoint (c⁻¹ * σ) f := by
    intro x
    by_cases hx : x ∈ f.support
    · left
      simpa only [Equiv.Perm.mul_apply, h x hx, Equiv.Perm.inv_def] using Equiv.symm_apply_apply c x
    · right
      exact Equiv.Perm.notMem_support.mp hx
  have hc : (c⁻¹ * σ) * f * (c⁻¹ * σ)⁻¹ = f := by
    rw [hd.commute.eq, mul_assoc, mul_inv_cancel, mul_one]
  calc
    σ * f * σ⁻¹ = c * ((c⁻¹ * σ) * f * (c⁻¹ * σ)⁻¹) * c⁻¹ := by group
    _ = c * f * c⁻¹ := by rw [hc]

#print axioms proof_RubikPayload_sameOnSupportConjugation
