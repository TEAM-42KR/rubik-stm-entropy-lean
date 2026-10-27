import RubikSTM.SolvedRadii
import RubikSTM.OBTMDiameter
import RubikSTM.Diameter

section
set_option autoImplicit false

theorem rubik_stm_diameter_entropy :
    Filter.Tendsto Rubik.normalizedDiameter Filter.atTop (nhds Rubik.entropyConstant) :=
  @RubikSTM.rubik_stm_diameter_entropy
end

theorem rubik_obtm_diameter_entropy : Filter.Tendsto RubikOBTM.normalizedDiameter Filter.atTop (nhds Rubik.entropyConstant) := @RubikSTM.rubik_obtm_diameter_entropy

theorem rubik_stm_solved_radius_entropy :
    Filter.Tendsto Rubik.normalizedSolvedRadius Filter.atTop (nhds Rubik.entropyConstant) :=
  @RubikSTM.rubik_stm_solved_radius_entropy

theorem rubik_stm_solved_looking_radius_entropy :
    Filter.Tendsto Rubik.normalizedSolvedLookingRadius Filter.atTop (nhds Rubik.entropyConstant) :=
  @RubikSTM.rubik_stm_solved_looking_radius_entropy

theorem rubik_obtm_solved_radius_entropy :
    Filter.Tendsto RubikOBTM.normalizedSolvedRadius Filter.atTop (nhds Rubik.entropyConstant) :=
  @RubikSTM.rubik_obtm_solved_radius_entropy

theorem rubik_obtm_solved_looking_radius_entropy :
    Filter.Tendsto RubikOBTM.normalizedSolvedLookingRadius Filter.atTop (nhds Rubik.entropyConstant) :=
  @RubikSTM.rubik_obtm_solved_looking_radius_entropy
