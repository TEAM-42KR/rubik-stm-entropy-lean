import RubikSTM.Lemmas.Construction.EntropySharpDiameter

section
set_option autoImplicit false

theorem RubikSTM.rubik_stm_diameter_entropy :
    Filter.Tendsto Rubik.normalizedDiameter Filter.atTop (nhds Rubik.entropyConstant) :=
  @RubikConstruction.EntropySharpDiameter
end
