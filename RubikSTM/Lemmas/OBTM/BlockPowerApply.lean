import RubikSTM.Proofs.OBTM.BlockPowerApply
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikOBTM.block_power_apply :
    ∀ {n : ℕ} (a : Rubik.Axis) (side : Bool) (k : Fin (n - 1)) (j : ℕ) (s : Rubik.Sticker n), (RubikOBTM.blockQuarter n a side k ^ j) s = if RubikOBTM.selected a side k (Rubik.coordinate s.val.1 a) then (Rubik.surfaceRotation n a ^ j) s else s :=
  @proof_RubikOBTM_block_power_apply
