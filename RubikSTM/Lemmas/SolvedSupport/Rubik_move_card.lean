import RubikSTM.Proofs.SolvedSupport.Rubik_move_card
import RubikSTM.Definitions.Geometry.StmGraph
set_option autoImplicit false

theorem Rubik.move_card :
    ∀ (n : ℕ), Fintype.card (Rubik.Move n) = 9 * n :=
  @proof_Rubik_move_card
