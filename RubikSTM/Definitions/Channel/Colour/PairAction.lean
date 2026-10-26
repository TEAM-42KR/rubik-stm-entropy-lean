import Mathlib
import RubikSTM.Definitions.Channel.Colour.OrbitAction
set_option autoImplicit false

def RubikChannel.Colour.pairAction {V Colour : Type*} (κ : V → Colour) :
    (Equiv.Perm V × Equiv.Perm V) →*
      Equiv.Perm (RubikChannel.Colour.Orbit κ × RubikChannel.Colour.Orbit κ) where
  toFun g := (RubikChannel.Colour.orbitAction κ g.1).prodCongr
    (RubikChannel.Colour.orbitAction κ g.2)
  map_one' := by ext x <;> rfl
  map_mul' g h := by ext x <;> rfl
