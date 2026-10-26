import Mathlib
import RubikSTM.Definitions.Channel.DisjointFourCycleAlphabet
import RubikSTM.Definitions.Orbits.SwapPhi
import RubikSTM.Lemmas.Payloads.PairAlphabetConjugate
import RubikSTM.Lemmas.Payloads.BaselineAlphabet
set_option autoImplicit false

theorem proof_RubikPayload_diagonalConjugator (g : Equiv.Perm (Fin 24) × Equiv.Perm (Fin 24))
  (hg : g ∈ RubikChannel.disjointFourCycleAlphabet (Fin 24)) :
  ∃ σ : Equiv.Perm (Fin 24),
    σ * RubikGeometry.gen7 * σ⁻¹ = g.1 ∧ σ * RubikOrbit.minusB * σ⁻¹ = g.2 := by
  exact RubikPayload.pairAlphabetConjugate _ g RubikPayload.baselineAlphabet hg

#print axioms proof_RubikPayload_diagonalConjugator
