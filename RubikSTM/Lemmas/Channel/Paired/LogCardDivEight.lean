import RubikSTM.Proofs.Channel.Paired.LogCardDivEight
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Definitions.Channel.Paired.P
set_option autoImplicit false

theorem RubikChannel.Paired.log_card_div_eight :
    Real.log (Fintype.card RubikChannel.Paired.State : ℝ) / 8 = Rubik.entropyConstant :=
  @proof_RubikChannel_Paired_log_card_div_eight
