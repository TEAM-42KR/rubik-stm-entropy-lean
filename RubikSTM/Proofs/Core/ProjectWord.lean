import RubikSTM.Definitions.Core.CoreAction
import RubikSTM.Lemmas.Core.ProjectMove
set_option autoImplicit false

open Rubik RubikCore

theorem proof_RubikCore_project_word {n : ℕ} (w : List (Move n)) (c : Colouring n) :
    project (applyWord w c) = w.foldl (fun q m => coreAction m q) (project c) := by
  induction w generalizing c with
  | nil => rfl
  | cons m w ih =>
    simpa only [applyWord, List.foldl_cons, RubikCore.project_move] using ih (applyMove m c)

#print axioms proof_RubikCore_project_word
