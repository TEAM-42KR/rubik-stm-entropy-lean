import RubikSTM.Proofs.OBTM.Compiler.NativeLayoutRowsCard
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
set_option autoImplicit false

theorem RubikOBTMCompiler.native_layout_rows_card :
    ∀ {n k : ℕ} {X : Finset (Fin n)}
  (P : RubikOBTMCompiler.OddLayout X k) (j : Fin P.blocks), (P.rows j).card ≤ k :=
  @proof_RubikOBTMCompiler_native_layout_rows_card
