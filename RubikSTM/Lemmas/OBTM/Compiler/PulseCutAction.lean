import RubikSTM.Proofs.OBTM.Compiler.PulseCutAction
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
set_option autoImplicit false

theorem RubikOBTMCompiler.pulse_cut_action :
    ∀ {n : ℕ} {A Y : Finset (Fin n)} (h : RubikPayload.Admissible A Y) (hord : Set.OrdConnected (Y : Set (Fin n))) (B : Finset (Fin n)) (hB : B ⊆ Y) {a b : Fin n} (ha : a ∈ A) (hb : b ∈ Y), (∀ i, RubikOBTMCompiler.cutBaseline Y B (RubikOBTM.Band.plus a b i) = RubikOBTM.Band.plus a b ((RubikOBTMCompiler.halfPair ^ (B.filter (fun d => b ≤ d)).card).1 i)) ∧ (∀ i, RubikOBTMCompiler.cutBaseline Y B (RubikOBTM.Band.minus a b i) = RubikOBTM.Band.minus a b ((RubikOBTMCompiler.halfPair ^ (B.filter (fun d => b ≤ d)).card).2 i)) :=
  @proof_RubikOBTMCompiler_pulse_cut_action
