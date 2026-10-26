import RubikSTM.Proofs.OBTM.Compiler.NativeVectorData
import RubikSTM.Definitions.OBTM.Compiler.VectorAction
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
set_option autoImplicit false

theorem RubikOBTMCompiler.native_vector_data :
    ∀ {k : ℕ} (ps : List (Fin k → RubikPayload.Pair)) (x : Fin k → RubikChannel.Paired.State) (r : Fin k), RubikRectangle.data (((ps.map (fun g => RubikOBTMCompiler.coordinatePerm (fun z => RubikChannel.Colour.pairAction RubikChannel.Paired.Seed (g z)))).reverse.prod) x r) = RubikRectangle.rawAction ((ps.map (fun g => g r)).reverse.prod) (RubikRectangle.data (x r)) :=
  @proof_RubikOBTMCompiler_native_vector_data
