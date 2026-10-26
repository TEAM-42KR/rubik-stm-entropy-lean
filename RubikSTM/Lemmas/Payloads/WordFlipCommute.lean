import RubikSTM.Proofs.Payloads.WordFlipCommute
import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
set_option autoImplicit false

theorem RubikPayload.wordFlipCommute :
    ∀ {n : ℕ} (b : Fin n) (hb : 0 < b.val ∧ b.val + 1 < n)
  (w : List (Rubik.Move n))
  (hw : ∀ m ∈ w, m.2.1 ≠ b ∧ m.2.1 ≠ b.rev), Commute (RubikBand.wordPerm w) (RubikIntertwiner.surfaceFlip b hb) :=
  @proof_RubikPayload_wordFlipCommute
