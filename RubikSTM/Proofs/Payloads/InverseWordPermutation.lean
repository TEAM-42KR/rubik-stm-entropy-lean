import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
import RubikSTM.Lemmas.Payloads.InverseMovePermutation
set_option autoImplicit false

theorem proof_RubikPayload_inverseWordPermutation {n : ℕ} (w : List (Rubik.Move n)) :
  RubikBand.wordPerm (RubikPayload.inverseWord w) = (RubikBand.wordPerm w)⁻¹ ∧
    (RubikPayload.inverseWord w).length = w.length := by
  constructor
  · simp [RubikPayload.inverseWord, RubikBand.wordPerm, List.map_reverse,
      List.map_map, Function.comp_def, RubikPayload.inverseMovePermutation, List.prod_inv_reverse]
  · simp [RubikPayload.inverseWord]

#print axioms proof_RubikPayload_inverseWordPermutation
