import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
import RubikSTM.Definitions.Wings.SolverWord
set_option autoImplicit false

theorem proof_RubikPayload_inverseMovePermutation {n : ℕ} (m : Rubik.Move n) :
  Rubik.movePermutation (RubikPayload.inverseMove m) = (Rubik.movePermutation m)⁻¹ := by
  have hp : Rubik.movePermutation (RubikPayload.inverseMove m) * Rubik.movePermutation m = 1 := by
    change Rubik.sliceQuarter n m.1 m.2.1 ^ (m.2.2.rev.val + 1) *
      Rubik.sliceQuarter n m.1 m.2.1 ^ (m.2.2.val + 1) = 1
    rw [← pow_add]
    have he : m.2.2.rev.val + 1 + (m.2.2.val + 1) = 4 := by
      change (3-(m.2.2.val+1))+1+(m.2.2.val+1)=4
      have := m.2.2.isLt
      omega
    rw [he, Rubik.sliceQuarter_order_four]
  calc
    Rubik.movePermutation (RubikPayload.inverseMove m) =
      (Rubik.movePermutation (RubikPayload.inverseMove m) * Rubik.movePermutation m) *
        (Rubik.movePermutation m)⁻¹ := by group
    _ = (Rubik.movePermutation m)⁻¹ := by rw [hp, one_mul]

#print axioms proof_RubikPayload_inverseMovePermutation
