import RubikSTM.Definitions.OBTM.Band.CleanAction
set_option autoImplicit false
open Rubik RubikOBTM RubikOBTM.Band
set_option maxHeartbeats 600000

theorem proof_RubikOBTM_Band_wordPerm_append {n : ℕ} (w z : List (BlockMove n)) :
    wordPerm (w ++ z) = wordPerm z * wordPerm w := by
  simp [wordPerm, List.reverse_append]
