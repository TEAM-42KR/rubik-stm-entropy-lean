import RubikSTM.Proofs.OBTM.Compiler.CutBaselineNative
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
set_option autoImplicit false

theorem RubikOBTMCompiler.cut_baseline_native :
    ∀ {n : ℕ} (Y B : Finset (Fin n))
  (hB : B ⊆ Y) (hY : ∀ d∈Y, 1 ≤ d.val ∧ d.val < n-1), ∃ w : List (RubikOBTM.BlockMove n), w.length ≤ B.card+1 ∧
    RubikOBTM.Band.wordPerm w = RubikOBTMCompiler.cutBaseline Y B ∧
    RubikOBTMCompiler.cutBaseline Y B ^ 2 = 1 :=
  @proof_RubikOBTMCompiler_cut_baseline_native
