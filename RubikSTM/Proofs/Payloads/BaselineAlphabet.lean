import Mathlib
import RubikSTM.Definitions.Channel.DisjointFourCycleAlphabet
import RubikSTM.Definitions.Orbits.SwapPhi
set_option autoImplicit false

theorem proof_RubikPayload_baselineAlphabet :
  (RubikGeometry.gen7, RubikOrbit.minusB) ∈ RubikChannel.disjointFourCycleAlphabet (Fin 24) := by
  have hp : RubikGeometry.gen7 = ([2,4,15,17] : List (Fin 24)).formPerm := by decide
  have hm : RubikOrbit.minusB = ([3,13,16,19] : List (Fin 24)).formPerm := by decide
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [hp]
    exact List.isCycle_formPerm (by decide) (by decide)
  · decide
  · rw [hm]
    exact List.isCycle_formPerm (by decide) (by decide)
  · decide
  · decide

#print axioms proof_RubikPayload_baselineAlphabet
