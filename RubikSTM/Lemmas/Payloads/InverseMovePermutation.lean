import RubikSTM.Proofs.Payloads.InverseMovePermutation
import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
set_option autoImplicit false

theorem RubikPayload.inverseMovePermutation :
    ∀ {n : ℕ} (m : Rubik.Move n), Rubik.movePermutation (RubikPayload.inverseMove m) = (Rubik.movePermutation m)⁻¹ :=
  @proof_RubikPayload_inverseMovePermutation
