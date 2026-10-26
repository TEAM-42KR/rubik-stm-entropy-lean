import RubikSTM.Proofs.OBTM.Band.SingleIntersectionRange
import RubikSTM.Definitions.OBTM.Band.CleanAction
set_option autoImplicit false

theorem RubikOBTM.Band.single_intersection_range :
    ∀ {n : ℕ} (a d : Fin n) (ha : 1 ≤ a.val) (hd : 1 ≤ d.val) (has : 2*a.val+2 ≤ n) (hds : 2*d.val+2 ≤ n) (had : a ≠ d) (s : Rubik.Sticker n), (RubikBand.Band a s ∧ RubikBand.Band d s) ↔ (s ∈ Set.range (RubikOBTM.Band.plus a d) ∨ s ∈ Set.range (RubikOBTM.Band.minus a d)) :=
  @proof_RubikOBTM_Band_single_intersection_range
