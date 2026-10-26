import RubikSTM.Proofs.OBTM.Compiler.PulseIntervalData
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
set_option autoImplicit false

theorem RubikOBTMCompiler.pulse_interval_data :
    ∀ {n : ℕ} {A Y : Finset (Fin n)} (h : RubikPayload.Admissible A Y) (hord : Set.OrdConnected (Y : Set (Fin n))) (hY : Y.Nonempty), (∀ d : Fin n, d ∈ Y ↔ RubikOBTM.Band.InInterval (Y.min' hY) (Y.max' hY) d) ∧ (∀ a ∈ A, RubikOBTM.Band.Admissible n a (Y.min' hY) (Y.max' hY)) ∧ (∀ a ∈ A, ∀ s : Rubik.Sticker n, s ∈ RubikOBTM.Band.PairedRange a (Y.min' hY) (Y.max' hY) → RubikPayload.Rectangles A Y s) :=
  @proof_RubikOBTMCompiler_pulse_interval_data
