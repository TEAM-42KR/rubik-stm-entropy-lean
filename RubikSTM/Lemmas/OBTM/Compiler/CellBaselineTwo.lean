import RubikSTM.Proofs.OBTM.Compiler.CellBaselineTwo
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
set_option autoImplicit false

theorem RubikOBTMCompiler.cell_baseline_two :
    ∀ {n : ℕ} (Y : Finset (Fin n)) (b : Fin n), RubikOBTMCompiler.cellBaseline Y b ^ 2 = 1 :=
  @proof_RubikOBTMCompiler_cell_baseline_two
