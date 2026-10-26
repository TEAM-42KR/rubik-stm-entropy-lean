import RubikSTM.Proofs.OBTM.Band.SlabPrefixDifference
import RubikSTM.Definitions.OBTM.Band.SlabWord
set_option autoImplicit false

theorem RubikOBTM.Band.slab_prefix_difference :
    ∀ {n : ℕ} (u v : Fin n) (hu : 1 ≤ u.val) (huv : u.val ≤ v.val) (hv : v.val < n-1), RubikOBTM.Band.slabPerm u v = RubikOBTM.blockQuarter n 2 true ⟨v.val,hv⟩ * (RubikOBTM.blockQuarter n 2 true ⟨u.val-1,by omega⟩)⁻¹ :=
  @proof_RubikOBTM_Band_slab_prefix_difference
