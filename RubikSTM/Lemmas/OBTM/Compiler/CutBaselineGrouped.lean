import RubikSTM.Proofs.OBTM.Compiler.CutBaselineGrouped
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
set_option autoImplicit false

theorem RubikOBTMCompiler.cut_baseline_grouped :
    ∀ {n : ℕ} {P : Type*} [DecidableEq P]
  (Y : Finset (Fin n)) (w : Fin n → P) (A : Finset P) (hw : ∀ d∈Y, w d∈A), (A.toList.map (fun p => RubikOBTMCompiler.cutBaseline Y (Y.filter (fun d => w d=p)))).reverse.prod =
    RubikOBTMCompiler.fullBaseline Y :=
  @proof_RubikOBTMCompiler_cut_baseline_grouped
