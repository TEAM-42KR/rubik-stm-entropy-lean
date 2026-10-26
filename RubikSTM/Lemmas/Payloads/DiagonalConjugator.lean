import RubikSTM.Proofs.Payloads.DiagonalConjugator
import Mathlib
import RubikSTM.Definitions.Channel.DisjointFourCycleAlphabet
import RubikSTM.Definitions.Orbits.SwapPhi
set_option autoImplicit false

theorem RubikPayload.diagonalConjugator :
    ∀ (g : Equiv.Perm (Fin 24) × Equiv.Perm (Fin 24))
  (hg : g ∈ RubikChannel.disjointFourCycleAlphabet (Fin 24)), ∃ σ : Equiv.Perm (Fin 24),
    σ * RubikGeometry.gen7 * σ⁻¹ = g.1 ∧ σ * RubikOrbit.minusB * σ⁻¹ = g.2 :=
  @proof_RubikPayload_diagonalConjugator
