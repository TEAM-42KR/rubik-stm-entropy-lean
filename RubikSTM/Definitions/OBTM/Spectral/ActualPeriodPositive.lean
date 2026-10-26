import RubikSTM.Definitions.OBTM.Finite.PhaseAct
import RubikSTM.Definitions.OBTM.Spectral.SingleWordMatrix
set_option autoImplicit false

namespace RubikOBTM.Spectral

noncomputable def actualPeriodPositive : 0 < RubikOBTM.Finite.period := Fintype.card_pos

noncomputable def actualAlphabetNonempty : RubikOBTM.Finite.nativeC.Nonempty :=
  ⟨RubikOBTM.Finite.nativeEquiv RubikOBTM.Finite.nativeWitness,
    (RubikOBTM.Finite.nativeEquiv RubikOBTM.Finite.nativeWitness).property⟩

end RubikOBTM.Spectral
