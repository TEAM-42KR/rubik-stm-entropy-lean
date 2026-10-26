import RubikSTM.Diameter

section
set_option autoImplicit false

theorem rubik_stm_diameter_entropy :
    Filter.Tendsto Rubik.normalizedDiameter Filter.atTop (nhds Rubik.entropyConstant) :=
  @RubikSTM.rubik_stm_diameter_entropy
end
