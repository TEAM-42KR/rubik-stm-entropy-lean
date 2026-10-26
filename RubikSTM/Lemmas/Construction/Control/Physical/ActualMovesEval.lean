import RubikSTM.Proofs.Construction.Control.Physical.ActualMovesEval
import RubikSTM.Definitions.Construction.Control.Physical.ActualMoves
set_option autoImplicit false

theorem RubikConstruction.Control.Physical.actual_moves_eval :
    ∀ {n : ℕ} (a : Fin n) (letters : List RubikConstruction.Control.Physical.SignedLetter), RubikConstruction.Control.Physical.chronological (RubikConstruction.Control.Physical.actualMoves a letters) = RubikConstruction.Control.physicalEval a (FreeGroup.mk letters) :=
  @proof_RubikConstruction_Control_Physical_actual_moves_eval
