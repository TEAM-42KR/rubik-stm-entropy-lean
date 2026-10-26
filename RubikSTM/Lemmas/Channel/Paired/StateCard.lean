import RubikSTM.Proofs.Channel.Paired.StateCard
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Definitions.Channel.Paired.P
set_option autoImplicit false

theorem RubikChannel.Paired.StateCard :
    Fintype.card RubikChannel.Paired.State = RubikGeometry.orbitColourings ^ 2 :=
  @proof_RubikChannel_Paired_StateCard
