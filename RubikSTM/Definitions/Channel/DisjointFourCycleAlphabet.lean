import Mathlib.GroupTheory.SpecificGroups.Alternating
set_option autoImplicit false

def RubikChannel.disjointFourCycleAlphabet (V : Type*) [Fintype V] [DecidableEq V] :
    Set (Equiv.Perm V × Equiv.Perm V) :=
  {g | (g.1.IsCycle ∧ g.1.support.card = 4) ∧
       (g.2.IsCycle ∧ g.2.support.card = 4) ∧
       Disjoint g.1.support g.2.support}
