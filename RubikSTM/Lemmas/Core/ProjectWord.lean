import RubikSTM.Proofs.Core.ProjectWord
import RubikSTM.Definitions.Core.CoreAction
set_option autoImplicit false

theorem RubikCore.project_word :
    ∀ {n : ℕ} (w : List (Rubik.Move n)) (c : Rubik.Colouring n), RubikCore.project (Rubik.applyWord w c) = w.foldl (fun q m => RubikCore.coreAction m q) (RubikCore.project c) :=
  @proof_RubikCore_project_word
