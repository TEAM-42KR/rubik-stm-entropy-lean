import RubikSTM.Proofs.Construction.EntropySharpDiameter
import RubikSTM.Definitions.Geometry.StmGraph
set_option autoImplicit false

theorem RubikConstruction.EntropySharpDiameter :
    Filter.Tendsto Rubik.normalizedDiameter Filter.atTop (nhds Rubik.entropyConstant) :=
  @proof_RubikConstruction_EntropySharpDiameter
