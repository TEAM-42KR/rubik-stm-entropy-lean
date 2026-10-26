import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
import RubikSTM.Definitions.Core.CoreAction
import RubikSTM.Lemmas.WordConstruction.PhysicalWordColouring
import RubikSTM.Lemmas.Payloads.InverseWordPermutation
set_option autoImplicit false

theorem proof_RubikGlobalWord_undo_word {n : ℕ} (w : List (Rubik.Move n)) (c : Rubik.Colouring n) :
  Rubik.applyWord (RubikPayload.inverseWord w) (Rubik.applyWord w c) = c := by
  funext s
  rw [RubikCompiler.physicalWordColouring, RubikCompiler.physicalWordColouring]
  change c ((RubikBand.wordPerm w)⁻¹ ((RubikBand.wordPerm (RubikPayload.inverseWord w))⁻¹ s)) = c s
  rw [(RubikPayload.inverseWordPermutation w).1, inv_inv]
  exact congrArg c (Equiv.symm_apply_apply _ _)

#print axioms proof_RubikGlobalWord_undo_word
