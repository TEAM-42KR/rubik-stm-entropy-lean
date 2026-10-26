import RubikSTM.Proofs.OBTM.Compiler.NativePairColouring
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
set_option autoImplicit false

theorem RubikOBTMCompiler.native_pair_colouring :
    ∀ {n : ℕ} (a b : Fin n)
  (w : List (RubikOBTM.BlockMove n)) (g : RubikPayload.Pair)
  (h : RubikOBTMCompiler.NativeActsPair a b w g) (c : Rubik.Colouring n), RubikOBTMCompiler.commonView (RubikOBTM.applyBlockWord w c) a b =
    RubikRectangle.rawAction g (RubikOBTMCompiler.commonView c a b) :=
  @proof_RubikOBTMCompiler_native_pair_colouring
