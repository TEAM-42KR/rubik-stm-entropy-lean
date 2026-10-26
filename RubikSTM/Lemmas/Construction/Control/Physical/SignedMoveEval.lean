import RubikSTM.Proofs.Construction.Control.Physical.SignedMoveEval
import RubikSTM.Definitions.Construction.Control.Physical.ActualMoves
set_option autoImplicit false

theorem RubikConstruction.Control.Physical.signed_move_eval :
    ∀ {n : ℕ} (a : Fin n) (t : RubikConstruction.Control.Physical.SignedLetter), Rubik.movePermutation (RubikConstruction.Control.Physical.signedMove a t) = if t.2 then RubikConstruction.Control.physicalAtom a t.1 else (RubikConstruction.Control.physicalAtom a t.1)⁻¹ :=
  @proof_RubikConstruction_Control_Physical_signed_move_eval
