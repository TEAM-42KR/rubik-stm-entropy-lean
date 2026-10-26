import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_native_layout_rows_card {n k : ℕ} {X : Finset (Fin n)}
  (P : RubikOBTMCompiler.OddLayout X k) (j : Fin P.blocks) : (P.rows j).card ≤ k := by
  classical
  have h := Finset.card_le_card_of_injOn P.row
    (s:=P.rows j) (t:=Finset.univ) (by intro a ha; exact Finset.mem_univ _)
    (by
      intro a ha b hb he
      have hA := Finset.mem_filter.mp ha
      have hB := Finset.mem_filter.mp hb
      exact P.injective a hA.1 b hB.1 (hA.2.trans hB.2.symm) he)
  simpa using h

#print axioms proof_RubikOBTMCompiler_native_layout_rows_card
