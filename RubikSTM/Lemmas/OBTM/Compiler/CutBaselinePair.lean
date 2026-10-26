import RubikSTM.Proofs.OBTM.Compiler.CutBaselinePair
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
set_option autoImplicit false

theorem RubikOBTMCompiler.cut_baseline_pair :
    ∀ {n : ℕ} {A Y : Finset (Fin n)} (hAY : RubikPayload.Admissible A Y) (hY : Set.OrdConnected (Y : Set (Fin n))) {a b : Fin n} (ha : a ∈ A) (hb : b ∈ Y) (B : Finset (Fin n)) (hB : B ⊆ Y), (∀ i, RubikOBTMCompiler.cutBaseline Y B (RubikOBTM.Band.plus a b i) = RubikOBTM.Band.plus a b ((RubikOBTMCompiler.halfPair ^ (B.filter (fun d => b ≤ d)).card).1 i)) ∧ (∀ i, RubikOBTMCompiler.cutBaseline Y B (RubikOBTM.Band.minus a b i) = RubikOBTM.Band.minus a b ((RubikOBTMCompiler.halfPair ^ (B.filter (fun d => b ≤ d)).card).2 i)) :=
  @proof_RubikOBTMCompiler_cut_baseline_pair
