import RubikSTM.Definitions.Channel.Transition
import RubikSTM.Definitions.Channel.Colour.PairAction
import RubikSTM.Definitions.Channel.DisjointFourCycleAlphabet
import RubikSTM.Definitions.OrbitGeometry.NormalTable
import Mathlib.GroupTheory.Perm.Cycle.Concrete
set_option autoImplicit false

noncomputable section
open scoped Classical

namespace RubikChannel.Paired

instance orbitFinite {V Colour : Type*} [Finite V] (κ : V → Colour) :
    Finite (RubikChannel.Colour.Orbit κ) := by
  let f : Equiv.Perm V → RubikChannel.Colour.Orbit κ := fun σ => ⟨κ ∘ σ, ⟨σ,rfl⟩⟩
  apply Finite.of_surjective f
  intro x
  obtain ⟨σ,hσ⟩ := x.property
  exact ⟨σ, Subtype.ext hσ.symm⟩

abbrev Seed := RubikGeometry.normalTable
abbrev State := RubikChannel.Colour.Orbit Seed × RubikChannel.Colour.Orbit Seed
abbrev Letter := {g : Equiv.Perm (Fin 24) × Equiv.Perm (Fin 24) //
  g ∈ RubikChannel.disjointFourCycleAlphabet (Fin 24)}

instance stateFinite : Finite State := inferInstance
instance stateFintype : Fintype State := Fintype.ofFinite State
instance stateDecidableEq : DecidableEq State := Classical.decEq State
instance letterFintype : Fintype Letter := Fintype.ofFinite Letter
instance letterDecidableEq : DecidableEq Letter := Classical.decEq Letter

def seedState : State := (⟨Seed,⟨1,rfl⟩⟩,⟨Seed,⟨1,rfl⟩⟩)
instance stateNonempty : Nonempty State := ⟨seedState⟩

def loopLetter : Letter := by
  let a : Equiv.Perm (Fin 24) := [0,1,2,3].formPerm
  let b : Equiv.Perm (Fin 24) := [20,21,22,23].formPerm
  have hA : ([0,1,2,3] : List (Fin 24)).Nodup := by decide
  have hB : ([20,21,22,23] : List (Fin 24)).Nodup := by decide
  have hsA := List.support_formPerm_of_nodup [0,1,2,3] hA (by simp)
  have hsB := List.support_formPerm_of_nodup [20,21,22,23] hB (by simp)
  refine ⟨(a,b), ⟨⟨List.isCycle_formPerm hA (by decide), ?_⟩,
    ⟨List.isCycle_formPerm hB (by decide), ?_⟩, ?_⟩⟩
  · change [0,1,2,3].formPerm.support.card = 4
    rw [hsA, List.toFinset_card_of_nodup hA]
    rfl
  · change [20,21,22,23].formPerm.support.card = 4
    rw [hsB, List.toFinset_card_of_nodup hB]
    rfl
  · change Disjoint [0,1,2,3].formPerm.support [20,21,22,23].formPerm.support
    rw [hsA,hsB]
    decide

instance letterNonempty : Nonempty Letter := ⟨loopLetter⟩

def μ : RubikJanson.FiniteLaw Letter := RubikJanson.uniformLaw inferInstance

def act (c : Letter) : Equiv.Perm State := RubikChannel.Colour.pairAction Seed c.val

def P : Matrix State State ℝ := RubikChannel.transition μ act

end RubikChannel.Paired
