import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Lemmas.OBTM.BlockPowerApply
import RubikSTM.Lemmas.OBTM.SurfaceRotationFour
set_option autoImplicit false

theorem proof_RubikOBTM_block_inverse {n : ℕ} (m : RubikOBTM.BlockMove n) :
    ∃ r : RubikOBTM.BlockMove n, RubikOBTM.blockPermutation r = (RubikOBTM.blockPermutation m)⁻¹ := by
  let r : RubikOBTM.BlockMove n := (m.1, m.2.1, m.2.2.1, m.2.2.2.rev)
  have hfour : RubikOBTM.blockQuarter n m.1 m.2.1 m.2.2.1 ^ 4 = 1 := by
    apply Equiv.ext
    intro s
    rw [RubikOBTM.block_power_apply, RubikOBTM.surfaceRotation_four]
    simp
  refine ⟨r, mul_eq_one_iff_eq_inv.mp ?_⟩
  change (RubikOBTM.blockQuarter n m.1 m.2.1 m.2.2.1 ^ (m.2.2.2.rev.val + 1)) *
    (RubikOBTM.blockQuarter n m.1 m.2.1 m.2.2.1 ^ (m.2.2.2.val + 1)) = 1
  rw [← pow_add]
  have hsum : m.2.2.2.rev.val + 1 + (m.2.2.2.val + 1) = 4 := by
    simp only [Fin.val_rev]
    have := m.2.2.2.isLt
    omega
  rw [hsum, hfour]
