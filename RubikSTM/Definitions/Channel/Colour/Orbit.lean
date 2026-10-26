import Mathlib
set_option autoImplicit false

def RubikChannel.Colour.Orbit {V Colour : Type*} (κ : V → Colour) :=
  {f : V → Colour // ∃ σ : Equiv.Perm V, f = κ ∘ σ}
