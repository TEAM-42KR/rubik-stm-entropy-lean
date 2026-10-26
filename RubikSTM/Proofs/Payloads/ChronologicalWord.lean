import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
import RubikSTM.Lemmas.Construction.Control.Physical.ChronologicalAlgebra
set_option autoImplicit false

theorem proof_RubikPayload_chronologicalWord {n : ℕ} (w : List (Rubik.Move n)) :
  RubikConstruction.Control.Physical.chronological w = RubikBand.wordPerm w := by
  rw [RubikConstruction.Control.Physical.chronological_algebra]
  simp [RubikBand.wordPerm, List.map_reverse]

#print axioms proof_RubikPayload_chronologicalWord
