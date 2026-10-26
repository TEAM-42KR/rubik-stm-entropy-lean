import RubikSTM.Proofs.Payloads.PairedPayload
import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
set_option autoImplicit false

theorem RubikPayload.pairedPayload :
    ∃ C : ℕ, ∀ (n : ℕ) (A Y : Finset (Fin n)),
  RubikPayload.Admissible A Y → ∀ g : Fin n → RubikPayload.Pair,
    (∀ a ∈ A, g a ∈ RubikChannel.disjointFourCycleAlphabet (Fin 24)) →
    ∃ w : List (Rubik.Move n), w.length ≤ Y.card + C * (A.card + 1) ∧
      RubikPayload.Realizes A Y g w :=
  @proof_RubikPayload_pairedPayload
