import RubikSTM.Proofs.Payloads.SingleIndexWordAction
import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
set_option autoImplicit false

theorem RubikPayload.singleIndexWordAction :
    ∀ {n : ℕ} {I : Type*} [DecidableEq I] (rows : List I)
  (hnd : rows.Nodup) (a : I) (ws : I → List (Rubik.Move n))
  (lab : Fin 24 → Rubik.Sticker n) (σ : Equiv.Perm (Fin 24))
  (hstep : ∀ c ∈ rows, ∀ i, RubikBand.wordPerm (ws c) (lab i) =
    lab (if c = a then σ i else i)), ∀ i, RubikBand.wordPerm (rows.flatMap ws) (lab i) =
    lab (if a ∈ rows then σ i else i) :=
  @proof_RubikPayload_singleIndexWordAction
