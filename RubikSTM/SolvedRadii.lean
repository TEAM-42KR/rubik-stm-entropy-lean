import RubikSTM.Lemmas.Solved.STMSolvedRadiusEntropy
import RubikSTM.Lemmas.Solved.STMSolvedLookingRadiusEntropy
import RubikSTM.Lemmas.Solved.OBTMSolvedRadiusEntropy
import RubikSTM.Lemmas.Solved.OBTMSolvedLookingRadiusEntropy

namespace RubikSTM

theorem rubik_stm_solved_radius_entropy :
    Filter.Tendsto Rubik.normalizedSolvedRadius Filter.atTop (nhds Rubik.entropyConstant) :=
  @RubikSolved.STMSolvedRadiusEntropy

theorem rubik_stm_solved_looking_radius_entropy :
    Filter.Tendsto Rubik.normalizedSolvedLookingRadius Filter.atTop (nhds Rubik.entropyConstant) :=
  @RubikSolved.STMSolvedLookingRadiusEntropy

theorem rubik_obtm_solved_radius_entropy :
    Filter.Tendsto RubikOBTM.normalizedSolvedRadius Filter.atTop (nhds Rubik.entropyConstant) :=
  @RubikSolved.OBTMSolvedRadiusEntropy

theorem rubik_obtm_solved_looking_radius_entropy :
    Filter.Tendsto RubikOBTM.normalizedSolvedLookingRadius Filter.atTop (nhds Rubik.entropyConstant) :=
  @RubikSolved.OBTMSolvedLookingRadiusEntropy

end RubikSTM
