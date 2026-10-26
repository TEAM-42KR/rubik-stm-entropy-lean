import RubikSTM.Proofs.Core.ProjectMove
import RubikSTM.Definitions.Core.CoreAction
set_option autoImplicit false

theorem RubikCore.project_move :
    ∀ {n : ℕ} (m : Rubik.Move n) (c : Rubik.Colouring n), RubikCore.project (Rubik.applyMove m c) = RubikCore.coreAction m (RubikCore.project c) :=
  @proof_RubikCore_project_move
