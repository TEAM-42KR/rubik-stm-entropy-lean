import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Lemmas.OBTM.BlockReachable
set_option autoImplicit false

theorem proof_RubikOBTM_blockWord_reachable {n : ℕ} (w : List (RubikOBTM.BlockMove n)) (c : Rubik.Colouring n)
    (hc : Rubik.Reachable c) : Rubik.Reachable (RubikOBTM.applyBlockWord w c) := by
  induction w generalizing c with
  | nil => exact hc
  | cons m w ih =>
    exact ih (RubikOBTM.applyBlock m c) (RubikOBTM.block_reachable m c hc)
