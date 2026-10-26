import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_cell_baseline_two {n : ℕ} (Y : Finset (Fin n)) (b : Fin n) :
    RubikOBTMCompiler.cellBaseline Y b ^ 2 = 1 := by
  have h : RubikOBTMCompiler.halfPair ^ 2 = 1 := by
    decide
  unfold RubikOBTMCompiler.cellBaseline
  rw [← pow_mul,Nat.mul_comm, pow_mul,h,one_pow]
