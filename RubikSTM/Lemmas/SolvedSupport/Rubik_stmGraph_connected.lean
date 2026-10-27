import RubikSTM.Proofs.SolvedSupport.Rubik_stmGraph_connected
import RubikSTM.Definitions.Geometry.StmGraph
set_option autoImplicit false

theorem Rubik.stmGraph_connected :
    ∀ (n : ℕ), (Rubik.stmGraph n).Connected :=
  @proof_Rubik_stmGraph_connected
