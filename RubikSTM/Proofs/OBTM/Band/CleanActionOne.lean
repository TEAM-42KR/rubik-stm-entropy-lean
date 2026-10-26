import RubikSTM.Definitions.OBTM.Band.CleanAction
set_option autoImplicit false
open Rubik RubikOBTM RubikOBTM.Band
set_option maxHeartbeats 600000

theorem proof_RubikOBTM_Band_clean_action_one {n : ℕ} (a u v : Fin n) : CleanAction a u v 1 1 := by
  constructor
  · intro d hd i
    exact ⟨rfl,rfl⟩
  · intro s hs
    rfl
