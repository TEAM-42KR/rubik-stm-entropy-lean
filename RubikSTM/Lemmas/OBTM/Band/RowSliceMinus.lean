import RubikSTM.Proofs.OBTM.Band.RowSliceMinus
import RubikSTM.Definitions.OBTM.Band.CleanAction
set_option autoImplicit false

theorem RubikOBTM.Band.row_slice_minus :
    ∀ {n : ℕ} (a d : Fin n) (ha : 1 ≤ a.val) (hd : 1 ≤ d.val) (has : 2*a.val+2 ≤ n) (hds : 2*d.val+2 ≤ n) (had : a ≠ d) (ax : Fin 3) (i : Fin 24), RubikConstruction.Control.physicalAtom a (Sum.inr ax) (RubikOBTM.Band.minus a d i) = RubikOBTM.Band.minus a d (RubikConstruction.Control.finiteAtom (Sum.inr ax) i) :=
  @proof_RubikOBTM_Band_row_slice_minus
