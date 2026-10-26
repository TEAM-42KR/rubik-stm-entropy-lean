import RubikSTM.Definitions.ExceptionalCentres.DiagonalThreeCycle
set_option autoImplicit false

def RubikExceptional.diagQuarterMove {n : ℕ} (a : Fin n) : Fin 12 → Rubik.Move n :=
  ![(0,RubikGeometry.lo a,0), (0,a,0), (0,a.rev,0), (0,RubikGeometry.hi a,0),
    (1,RubikGeometry.lo a,0), (1,a,0), (1,a.rev,0), (1,RubikGeometry.hi a,0),
    (2,RubikGeometry.lo a,0), (2,a,0), (2,a.rev,0), (2,RubikGeometry.hi a,0)]
