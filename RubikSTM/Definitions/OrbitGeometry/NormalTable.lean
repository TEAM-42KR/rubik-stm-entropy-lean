import RubikSTM.Definitions.Geometry.StmGraph
set_option autoImplicit false

namespace RubikGeometry
open Rubik

def normalTable : Fin 24 → Normal :=
  ![(0, true), (0, true), (0, true), (0, true), (1, true), (2, true), (2, true), (2, true), (2, true), (1, false), (0, false), (0, false), (1, true), (1, true), (1, true), (0, false), (0, false), (1, false), (1, false), (1, false), (2, false), (2, false), (2, false), (2, false)]

end RubikGeometry
