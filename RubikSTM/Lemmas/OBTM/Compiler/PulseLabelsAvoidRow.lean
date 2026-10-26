import RubikSTM.Proofs.OBTM.Compiler.PulseLabelsAvoidRow
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
set_option autoImplicit false

theorem RubikOBTMCompiler.pulse_labels_avoid_row :
    ∀ {n : ℕ} {a b c : Fin n} (hg : RubikGeometry.Generic n a b) (hc : RubikPayload.Half c) (hca : c ≠ a) (hcb : c ≠ b) (i : Fin 24), ¬ RubikBand.Band c (RubikOBTM.Band.plus a b i) ∧ ¬ RubikBand.Band c (RubikOBTM.Band.minus a b i) :=
  @proof_RubikOBTMCompiler_pulse_labels_avoid_row
