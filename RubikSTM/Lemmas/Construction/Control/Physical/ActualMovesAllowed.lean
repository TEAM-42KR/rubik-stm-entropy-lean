import RubikSTM.Proofs.Construction.Control.Physical.ActualMovesAllowed
import RubikSTM.Definitions.Construction.Control.Physical.ActualMoves
set_option autoImplicit false

theorem RubikConstruction.Control.Physical.actual_moves_allowed :
    ∀ {n : ℕ} (a : Fin n) (letters : List RubikConstruction.Control.Physical.SignedLetter), ∀ m ∈ RubikConstruction.Control.Physical.actualMoves a letters, RubikConstruction.Control.Physical.Allowed a m :=
  @proof_RubikConstruction_Control_Physical_actual_moves_allowed
