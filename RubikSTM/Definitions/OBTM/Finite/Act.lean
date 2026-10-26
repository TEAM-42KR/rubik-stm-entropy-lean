import RubikSTM.Definitions.Channel.Paired.P
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.GroupTheory.SpecificGroups.KleinFour
set_option autoImplicit false

namespace RubikOBTM.Finite
open Equiv Equiv.Perm
open scoped Classical

abbrev A := alternatingGroup (Fin 24)
abbrev G := A × A
abbrev Z := RubikChannel.Paired.State
abbrev Phase := A
abbrev Toggle := Multiplicative (ZMod 2 × ZMod 2)
abbrev Nonzero := {v : Toggle // v ≠ 1}
abbrev Native := Nonzero × Nonzero

def togglePerm (v : Toggle) : Perm (Fin 24) :=
  if v.toAdd.1 = 0 then
    if v.toAdd.2 = 0 then 1 else swap 0 1 * swap 4 5
  else if v.toAdd.2 = 0 then swap 0 1 * swap 2 3 else swap 2 3 * swap 4 5

def base : Toggle →* A where
  toFun v := ⟨togglePerm v, by
    unfold togglePerm
    split_ifs <;> simp [mem_alternatingGroup]⟩
  map_one' := by decide
  map_mul' := by
    have h : ∀ u v : Toggle, togglePerm (u * v) = togglePerm u * togglePerm v := by decide
    intro u v
    exact Subtype.ext (h u v)

def embed (i : Phase) : Toggle →* A := (MulAut.conj i).toMonoidHom.comp base

def E (i : Phase) : Subgroup A := (embed i).range
def K (i : Phase) : Subgroup G := (E i).prod (E i)

def letter (i : Phase) (c : Native) : G := (embed i c.1.val, embed i c.2.val)

def inclusion : G →* (Perm (Fin 24) × Perm (Fin 24)) where
  toFun g := (g.1.val,g.2.val)
  map_one' := rfl
  map_mul' _ _ := rfl

def act : G →* Perm Z :=
  (RubikChannel.Colour.pairAction RubikChannel.Paired.Seed).comp inclusion

noncomputable def period : ℕ := Fintype.card Phase
noncomputable def phaseIndex : Phase ≃ Fin period := Fintype.equivFin Phase
noncomputable def phaseAt (i : Fin period) : Phase := phaseIndex.symm i

end RubikOBTM.Finite
