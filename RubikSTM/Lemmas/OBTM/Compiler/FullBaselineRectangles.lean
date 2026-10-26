import RubikSTM.Proofs.OBTM.Compiler.FullBaselineRectangles
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
set_option autoImplicit false

theorem RubikOBTMCompiler.full_baseline_rectangles :
    ∀ {n : ℕ} {A Y : Finset (Fin n)}
  (h : RubikPayload.Admissible A Y) (s : Rubik.Sticker n), RubikPayload.Rectangles A Y (RubikOBTMCompiler.fullBaseline Y s) ↔ RubikPayload.Rectangles A Y s :=
  @proof_RubikOBTMCompiler_full_baseline_rectangles
