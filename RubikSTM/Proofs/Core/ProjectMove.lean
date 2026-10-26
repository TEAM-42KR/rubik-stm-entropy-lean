import RubikSTM.Definitions.Core.CoreAction
set_option autoImplicit false

open Rubik RubikCore

theorem proof_RubikCore_project_move {n : ℕ} (m : Move n) (c : Colouring n) :
    project (applyMove m c) = coreAction m (project c) := by
  rfl

#print axioms proof_RubikCore_project_move
