import RubikSTM.Definitions.OBTM.Finite.Act
set_option autoImplicit false

namespace RubikOBTM.Finite

def doubledSubgroup {H : Type*} [Group H] (K : Subgroup H) (independent : Bool) :
    Subgroup (H × H) :=
  if independent then K.prod K else K.map ((MonoidHom.id H).prod (MonoidHom.id H))

end RubikOBTM.Finite
