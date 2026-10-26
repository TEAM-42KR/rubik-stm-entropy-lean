import Mathlib
import RubikSTM.Definitions.Channel.Colour.Orbit
set_option autoImplicit false

def RubikChannel.Colour.orbitAction {V Colour : Type*} (κ : V → Colour) :
    Equiv.Perm V →* Equiv.Perm (RubikChannel.Colour.Orbit κ) where
  toFun σ :=
    { toFun := fun f => ⟨f.val ∘ (σ⁻¹ : Equiv.Perm V), by
        obtain ⟨τ, hτ⟩ := f.property
        refine ⟨τ * σ⁻¹, ?_⟩
        ext i
        simp [hτ, Function.comp_def]⟩
      invFun := fun f => ⟨f.val ∘ σ, by
        obtain ⟨τ, hτ⟩ := f.property
        refine ⟨τ * σ, ?_⟩
        ext i
        simp [hτ, Function.comp_def]⟩
      left_inv := by intro f; apply Subtype.ext; funext i; simp [Function.comp_def]
      right_inv := by intro f; apply Subtype.ext; funext i; simp [Function.comp_def] }
  map_one' := by ext f i; rfl
  map_mul' σ τ := by ext f i; rfl
