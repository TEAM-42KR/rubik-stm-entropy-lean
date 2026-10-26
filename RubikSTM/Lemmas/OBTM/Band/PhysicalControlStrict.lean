import RubikSTM.Proofs.OBTM.Band.PhysicalControlStrict
import RubikSTM.Definitions.OBTM.Band.CleanAction
set_option autoImplicit false

theorem RubikOBTM.Band.physical_control_strict :
    ∀ {n : ℕ} (a : Fin n) (ha : 1 ≤ a.val) (has : 2*a.val+2 ≤ n) (ms : List (Rubik.Move n)) (hm : ∀ m ∈ ms, RubikConstruction.Control.Physical.Allowed a m) (hd : RubikConstruction.Control.Physical.chronological (RubikConstruction.Control.Physical.faceOnlyMoves a ms) = 1), RubikBand.StrictControl a ms :=
  @proof_RubikOBTM_Band_physical_control_strict
