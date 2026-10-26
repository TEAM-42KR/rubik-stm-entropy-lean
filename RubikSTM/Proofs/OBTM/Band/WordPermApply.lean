import RubikSTM.Definitions.OBTM.Band.CleanAction
set_option autoImplicit false
open Rubik RubikOBTM RubikOBTM.Band
set_option maxHeartbeats 600000

theorem proof_RubikOBTM_Band_wordPerm_apply {n : ℕ} (w : List (BlockMove n))
    (c : Colouring n) (s : Sticker n) : applyBlockWord w c s = c ((wordPerm w)⁻¹ s) := by
  induction w generalizing c with
  | nil => rfl
  | cons m ms ih =>
    rw [show applyBlockWord (m :: ms) c = applyBlockWord ms (applyBlock m c) from rfl, ih]
    simp [applyBlock, wordPerm, List.reverse_cons, mul_inv_rev]
