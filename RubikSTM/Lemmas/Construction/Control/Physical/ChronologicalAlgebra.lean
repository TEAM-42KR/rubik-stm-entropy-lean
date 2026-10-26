import RubikSTM.Proofs.Construction.Control.Physical.ChronologicalAlgebra
import RubikSTM.Definitions.Construction.Control.Physical.ActualMoves
set_option autoImplicit false

theorem RubikConstruction.Control.Physical.chronological_algebra :
    ∀ {n : ℕ} (ms : List (Rubik.Move n)), RubikConstruction.Control.Physical.chronological ms = (ms.reverse.map Rubik.movePermutation).prod :=
  @proof_RubikConstruction_Control_Physical_chronological_algebra
