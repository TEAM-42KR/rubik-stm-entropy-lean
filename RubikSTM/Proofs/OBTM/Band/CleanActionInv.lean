import RubikSTM.Definitions.OBTM.Band.CleanAction
set_option autoImplicit false
open Rubik RubikOBTM RubikOBTM.Band
set_option maxHeartbeats 600000

theorem proof_RubikOBTM_Band_clean_action_inv {n : ℕ} (a u v : Fin n) (p : PairPerm)
    (P : Equiv.Perm (Sticker n)) (hp : CleanAction a u v p P) :
    CleanAction a u v p⁻¹ P⁻¹ := by
  constructor
  · intro d hd i
    constructor
    · apply Equiv.Perm.inv_eq_iff_eq.mpr
      simpa using (hp.1 d hd (p.1⁻¹ i)).1.symm
    · apply Equiv.Perm.inv_eq_iff_eq.mpr
      simpa using (hp.1 d hd (p.2⁻¹ i)).2.symm
  · intro s hs
    apply Equiv.Perm.inv_eq_iff_eq.mpr
    exact (hp.2 s hs).symm
