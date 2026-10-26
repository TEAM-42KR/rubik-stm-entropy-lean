import Mathlib
import RubikSTM.Definitions.Channel.DisjointFourCycleAlphabet
import RubikSTM.Definitions.Orbits.SwapPhi
import RubikSTM.Lemmas.Payloads.PatchConjugators
set_option autoImplicit false

theorem proof_RubikPayload_pairAlphabetConjugate {V : Type*} [Fintype V] [DecidableEq V]
  (f g : Equiv.Perm V × Equiv.Perm V)
  (hf : f ∈ RubikChannel.disjointFourCycleAlphabet V)
  (hg : g ∈ RubikChannel.disjointFourCycleAlphabet V) :
  ∃ σ : Equiv.Perm V, σ * f.1 * σ⁻¹ = g.1 ∧ σ * f.2 * σ⁻¹ = g.2 := by
  rcases hf with ⟨⟨hf₁,hfc₁⟩,⟨hf₂,hfc₂⟩,hfd⟩
  rcases hg with ⟨⟨hg₁,hgc₁⟩,⟨hg₂,hgc₂⟩,hgd⟩
  have hc₁ : IsConj f.1 g.1 := Equiv.Perm.isConj_iff_cycleType_eq.mpr (by
    rw [hf₁.cycleType, hg₁.cycleType, hfc₁, hgc₁])
  have hc₂ : IsConj f.2 g.2 := Equiv.Perm.isConj_iff_cycleType_eq.mpr (by
    rw [hf₂.cycleType, hg₂.cycleType, hfc₂, hgc₂])
  obtain ⟨c₁,h₁⟩ := isConj_iff.mp hc₁
  obtain ⟨c₂,h₂⟩ := isConj_iff.mp hc₂
  exact RubikPayload.patchConjugators _ _ _ _ c₁ c₂ hfd hgd h₁ h₂

#print axioms proof_RubikPayload_pairAlphabetConjugate
