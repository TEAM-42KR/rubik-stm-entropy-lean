import RubikSTM.Proofs.Payloads.PairAlphabetConjugate
import Mathlib
import RubikSTM.Definitions.Channel.DisjointFourCycleAlphabet
import RubikSTM.Definitions.Orbits.SwapPhi
set_option autoImplicit false

theorem RubikPayload.pairAlphabetConjugate :
    ∀ {V : Type*} [Fintype V] [DecidableEq V]
  (f g : Equiv.Perm V × Equiv.Perm V)
  (hf : f ∈ RubikChannel.disjointFourCycleAlphabet V)
  (hg : g ∈ RubikChannel.disjointFourCycleAlphabet V), ∃ σ : Equiv.Perm V, σ * f.1 * σ⁻¹ = g.1 ∧ σ * f.2 * σ⁻¹ = g.2 :=
  @proof_RubikPayload_pairAlphabetConjugate
