import RubikSTM.Proofs.OBTM.Compiler.PulseCleanSetup
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
set_option autoImplicit false

theorem RubikOBTMCompiler.pulse_clean_setup :
    ∃ K : ℕ, ∀ {n : ℕ} (A Y : Finset (Fin n)), RubikPayload.Admissible A Y → Set.OrdConnected (Y : Set (Fin n)) → ∀ σ τ : Fin n → RubikOBTM.Finite.A, ∃ U : List (RubikOBTM.BlockMove n), U.length ≤ K*A.card ∧ (∀ a ∈ A, ∀ b ∈ Y, RubikOBTMCompiler.NativeActsPair a b U ((σ a).val,(τ a).val)) ∧ ∀ s : Rubik.Sticker n, ¬RubikPayload.Rectangles A Y s → RubikOBTM.Band.wordPerm U s = s :=
  @proof_RubikOBTMCompiler_pulse_clean_setup
