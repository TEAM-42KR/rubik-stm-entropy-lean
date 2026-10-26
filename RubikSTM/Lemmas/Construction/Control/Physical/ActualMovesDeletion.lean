import RubikSTM.Proofs.Construction.Control.Physical.ActualMovesDeletion
import RubikSTM.Definitions.Construction.Control.Physical.ActualMoves
set_option autoImplicit false

theorem RubikConstruction.Control.Physical.actual_moves_deletion :
    ∀ {n : ℕ} (a : Fin n) (ha : 1 ≤ a.val) (has : 2 * a.val + 2 ≤ n) (letters : List RubikConstruction.Control.Physical.SignedLetter), RubikConstruction.Control.Physical.chronological (RubikConstruction.Control.Physical.faceOnlyMoves a (RubikConstruction.Control.Physical.actualMoves a letters)) = RubikConstruction.Control.faceOnlyEval a (FreeGroup.mk letters) :=
  @proof_RubikConstruction_Control_Physical_actual_moves_deletion
