import RubikSTM.Definitions.OBTM.Compiler.VectorAction
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
import RubikSTM.Lemmas.Rectangles.DataAct
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_native_vector_data {k : ℕ} (ps : List (Fin k → RubikPayload.Pair))
    (x : Fin k → RubikChannel.Paired.State) (r : Fin k) :
    RubikRectangle.data (((ps.map (fun g => RubikOBTMCompiler.coordinatePerm
        (fun z => RubikChannel.Colour.pairAction RubikChannel.Paired.Seed (g z)))).reverse.prod) x r) =
      RubikRectangle.rawAction ((ps.map (fun g => g r)).reverse.prod)
        (RubikRectangle.data (x r)) := by
  induction ps generalizing x with
  | nil => rfl
  | cons g ps ih =>
    simp only [List.map_cons,List.reverse_cons,List.prod_append,List.prod_singleton,
      Equiv.Perm.mul_apply]
    rw [ih]
    change RubikRectangle.rawAction ((ps.map (fun g => g r)).reverse.prod)
      (RubikRectangle.data (RubikChannel.Colour.pairAction RubikChannel.Paired.Seed (g r) (x r))) = _
    rw [RubikRectangle.data_act]
    rfl
