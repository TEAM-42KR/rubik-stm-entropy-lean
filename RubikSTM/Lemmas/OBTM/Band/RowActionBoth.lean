import RubikSTM.Proofs.OBTM.Band.RowActionBoth
import RubikSTM.Definitions.OBTM.Band.CleanAction
set_option autoImplicit false

theorem RubikOBTM.Band.row_action_both :
    ∀ {n : ℕ} (a d : Fin n) (ha : 1 ≤ a.val) (hd : 1 ≤ d.val) (has : 2*a.val+2 ≤ n) (hds : 2*d.val+2 ≤ n) (had : a ≠ d) (w : RubikConstruction.Control.Word) (i : Fin 24), (RubikConstruction.Control.physicalEval a w (RubikOBTM.Band.plus a d i) = RubikOBTM.Band.plus a d (RubikConstruction.Control.finiteEval w i)) ∧ (RubikConstruction.Control.physicalEval a w (RubikOBTM.Band.minus a d i) = RubikOBTM.Band.minus a d (RubikConstruction.Control.finiteEval w i)) :=
  @proof_RubikOBTM_Band_row_action_both
