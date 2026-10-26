import RubikSTM.Proofs.OBTM.Compiler.NativePhaseOfPulse
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
set_option autoImplicit false

theorem RubikOBTMCompiler.native_phase_of_pulse :
    ∀ (C : ℕ) (hP : RubikOBTMCompiler.NativePulseInterface C) {n k : ℕ} (A Y : Finset (Fin n)) (hAY : RubikPayload.Admissible A Y) (hY : Set.OrdConnected (Y : Set (Fin n))) (p : RubikOBTM.Finite.Phase) (row : Fin n → Fin k) (D : Finset (Fin k → RubikOBTM.Finite.Intrinsic)) (hD : ∀ g ∈ D, ∀ z, g z ∈ RubikOBTM.Finite.nativeC) (choice : Fin n → Fin k → RubikOBTM.Finite.Intrinsic) (hchoice : ∀ d ∈ Y, choice d ∈ D), ∃ w : List (RubikOBTM.BlockMove n), w.length ≤ Y.card + C*(A.card+1)*D.card ∧ (∀ a ∈ A, ∀ b ∈ Y, RubikOBTMCompiler.NativeActsPair a b w (RubikOBTM.Finite.inclusion (RubikOBTM.Finite.phaseHom p ((∏ d ∈ Y.filter (fun d => b ≤ d), choice d) (row a))))) ∧ (∀ s : Rubik.Sticker n, ¬ RubikPayload.Rectangles A Y s → RubikOBTM.Band.wordPerm w s = RubikOBTMCompiler.fullBaseline Y s) :=
  @proof_RubikOBTMCompiler_native_phase_of_pulse
