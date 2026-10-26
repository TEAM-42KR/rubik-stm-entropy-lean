import RubikSTM.Proofs.Payloads.SameOnSupportConjugation
import Mathlib
import RubikSTM.Definitions.Channel.DisjointFourCycleAlphabet
import RubikSTM.Definitions.Orbits.SwapPhi
set_option autoImplicit false

theorem RubikPayload.sameOnSupportConjugation :
    ∀ {V : Type*} [Fintype V] [DecidableEq V]
  (f c σ : Equiv.Perm V) (h : ∀ x ∈ f.support, σ x = c x), σ * f * σ⁻¹ = c * f * c⁻¹ :=
  @proof_RubikPayload_sameOnSupportConjugation
