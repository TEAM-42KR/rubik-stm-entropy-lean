import Mathlib.GroupTheory.SpecificGroups.Alternating
set_option autoImplicit false

def RubikChannel.equalParitySubgroup (V : Type*) [Fintype V] [DecidableEq V] :
    Subgroup (Equiv.Perm V × Equiv.Perm V) :=
  ((Equiv.Perm.sign : Equiv.Perm V →* ℤˣ).comp
    (MonoidHom.fst (Equiv.Perm V) (Equiv.Perm V))).eqLocus
  ((Equiv.Perm.sign : Equiv.Perm V →* ℤˣ).comp
    (MonoidHom.snd (Equiv.Perm V) (Equiv.Perm V)))
