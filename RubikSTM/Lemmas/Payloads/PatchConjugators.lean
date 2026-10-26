import RubikSTM.Proofs.Payloads.PatchConjugators
import Mathlib
import RubikSTM.Definitions.Channel.DisjointFourCycleAlphabet
import RubikSTM.Definitions.Orbits.SwapPhi
set_option autoImplicit false

theorem RubikPayload.patchConjugators :
    ∀ {V : Type*} [Fintype V] [DecidableEq V]
  (f₁ f₂ g₁ g₂ c₁ c₂ : Equiv.Perm V)
  (hf : Disjoint f₁.support f₂.support) (hg : Disjoint g₁.support g₂.support)
  (h₁ : c₁ * f₁ * c₁⁻¹ = g₁) (h₂ : c₂ * f₂ * c₂⁻¹ = g₂), ∃ σ : Equiv.Perm V, σ * f₁ * σ⁻¹ = g₁ ∧ σ * f₂ * σ⁻¹ = g₂ :=
  @proof_RubikPayload_patchConjugators
