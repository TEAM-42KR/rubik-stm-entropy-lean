import Mathlib
import RubikSTM.Definitions.Channel.DisjointFourCycleAlphabet
import RubikSTM.Definitions.Orbits.SwapPhi
import RubikSTM.Lemmas.Payloads.SameOnSupportConjugation
set_option autoImplicit false

theorem proof_RubikPayload_patchConjugators {V : Type*} [Fintype V] [DecidableEq V]
  (f₁ f₂ g₁ g₂ c₁ c₂ : Equiv.Perm V)
  (hf : Disjoint f₁.support f₂.support) (hg : Disjoint g₁.support g₂.support)
  (h₁ : c₁ * f₁ * c₁⁻¹ = g₁) (h₂ : c₂ * f₂ * c₂⁻¹ = g₂) :
  ∃ σ : Equiv.Perm V, σ * f₁ * σ⁻¹ = g₁ ∧ σ * f₂ * σ⁻¹ = g₂ := by
  classical
  have mem₁ (x : V) : c₁ x ∈ g₁.support ↔ x ∈ f₁.support := by
    rw [← h₁, Equiv.Perm.support_conj]
    simp
  have mem₂ (x : V) : c₂ x ∈ g₂.support ↔ x ∈ f₂.support := by
    rw [← h₂, Equiv.Perm.support_conj]
    simp
  let D := Sum {x : V // x ∈ f₁.support} {x : V // x ∈ f₂.support}
  let left : D → V := Sum.elim Subtype.val Subtype.val
  let right : D → V := Sum.elim (fun x => c₁ x.val) (fun x => c₂ x.val)
  have hl : Function.Injective left := by
    intro x y h
    rcases x with x | x <;> rcases y with y | y
    · exact congrArg Sum.inl (Subtype.ext h)
    · have he : x.val = y.val := h
      exact (Finset.disjoint_left.mp hf x.property (he.symm ▸ y.property)).elim
    · have he : x.val = y.val := h
      exact (Finset.disjoint_left.mp hf y.property (he ▸ x.property)).elim
    · exact congrArg Sum.inr (Subtype.ext h)
  have hr : Function.Injective right := by
    intro x y h
    rcases x with x | x <;> rcases y with y | y
    · exact congrArg Sum.inl (Subtype.ext (c₁.injective h))
    · have he : c₁ x.val = c₂ y.val := h
      exact (Finset.disjoint_left.mp hg ((mem₁ x).mpr x.property)
        (he.symm ▸ (mem₂ y).mpr y.property)).elim
    · have he : c₂ x.val = c₁ y.val := h
      exact (Finset.disjoint_left.mp hg ((mem₁ y).mpr y.property)
        (he ▸ (mem₂ x).mpr x.property)).elim
    · exact congrArg Sum.inr (Subtype.ext (c₂.injective h))
  obtain ⟨σ, hext⟩ := Equiv.Perm.exists_extending_pair left right hl hr
  have hs₁ : ∀ x ∈ f₁.support, σ x = c₁ x := by
    intro x hx
    exact hext (Sum.inl ⟨x,hx⟩)
  have hs₂ : ∀ x ∈ f₂.support, σ x = c₂ x := by
    intro x hx
    exact hext (Sum.inr ⟨x,hx⟩)
  exact ⟨σ, (RubikPayload.sameOnSupportConjugation f₁ c₁ σ hs₁).trans h₁,
    (RubikPayload.sameOnSupportConjugation f₂ c₂ σ hs₂).trans h₂⟩

#print axioms proof_RubikPayload_patchConjugators
