import RubikSTM.Proofs.Payloads.AllowedAvoidsColumn
import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
set_option autoImplicit false

theorem RubikPayload.allowedAvoidsColumn :
    ∀ {n : ℕ} {a b : Fin n} (hg : RubikGeometry.Generic n a b)
  (w : List (Rubik.Move n)) (hw : RubikBand.AllowedControl a w), ∀ m ∈ w, m.2.1 ≠ b ∧ m.2.1 ≠ b.rev :=
  @proof_RubikPayload_allowedAvoidsColumn
