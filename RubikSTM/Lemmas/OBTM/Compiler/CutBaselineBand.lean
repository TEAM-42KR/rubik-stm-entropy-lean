import RubikSTM.Proofs.OBTM.Compiler.CutBaselineBand
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
set_option autoImplicit false

theorem RubikOBTMCompiler.cut_baseline_band :
    ∀ {n : ℕ} (Y B : Finset (Fin n))
  (a : Fin n) (s : Rubik.Sticker n), RubikBand.Band a (RubikOBTMCompiler.cutBaseline Y B s) ↔ RubikBand.Band a s :=
  @proof_RubikOBTMCompiler_cut_baseline_band
