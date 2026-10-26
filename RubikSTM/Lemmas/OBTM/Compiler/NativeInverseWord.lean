import RubikSTM.Proofs.OBTM.Compiler.NativeInverseWord
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeCoalescedWord
set_option autoImplicit false

theorem RubikOBTMCompiler.native_inverse_word :
    ∀ {n : ℕ} (U : List (RubikOBTM.BlockMove n)), ∃ V : List (RubikOBTM.BlockMove n), V.length=U.length ∧
    RubikOBTM.Band.wordPerm V = (RubikOBTM.Band.wordPerm U)⁻¹ :=
  @proof_RubikOBTMCompiler_native_inverse_word
