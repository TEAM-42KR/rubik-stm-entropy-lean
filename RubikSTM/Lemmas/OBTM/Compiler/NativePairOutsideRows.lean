import RubikSTM.Proofs.OBTM.Compiler.NativePairOutsideRows
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
set_option autoImplicit false

theorem RubikOBTMCompiler.native_pair_outside_rows :
    ∀ {n : ℕ} {X A Y : Finset (Fin n)} (hXY : RubikPayload.Admissible X Y) (hAX : A ⊆ X) {a b : Fin n} (ha : a ∈ X) (haA : a ∉ A) (hb : b ∈ Y) (i : Fin 24), ¬ RubikPayload.Rectangles A Y (RubikOBTM.Band.plus a b i) ∧ ¬ RubikPayload.Rectangles A Y (RubikOBTM.Band.minus a b i) :=
  @proof_RubikOBTMCompiler_native_pair_outside_rows
