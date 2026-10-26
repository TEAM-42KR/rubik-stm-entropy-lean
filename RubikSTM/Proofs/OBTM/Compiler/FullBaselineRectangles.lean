import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
import RubikSTM.Lemmas.Payloads.RectanglesBands
import RubikSTM.Lemmas.OBTM.Compiler.CutBaselineBand
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_full_baseline_rectangles {n : ℕ} {A Y : Finset (Fin n)}
  (h : RubikPayload.Admissible A Y) (s : Rubik.Sticker n) :
  RubikPayload.Rectangles A Y (RubikOBTMCompiler.fullBaseline Y s) ↔ RubikPayload.Rectangles A Y s := by
  rw [RubikPayload.rectanglesBands h,RubikPayload.rectanglesBands h]
  simp only [RubikBand.Bands,RubikOBTMCompiler.fullBaseline,RubikOBTMCompiler.cut_baseline_band]

#print axioms proof_RubikOBTMCompiler_full_baseline_rectangles
