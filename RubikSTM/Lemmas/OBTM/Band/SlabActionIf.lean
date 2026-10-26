import RubikSTM.Proofs.OBTM.Band.SlabActionIf
import RubikSTM.Definitions.OBTM.Band.SlabWord
set_option autoImplicit false

theorem RubikOBTM.Band.slab_action_if :
    ∀ {n : ℕ} (a u v : Fin n) (h : RubikOBTM.Band.Admissible n a u v) (b d : Fin n) (hb : RubikOBTM.Band.InInterval u v b) (hd : RubikOBTM.Band.InInterval u v d) (i : Fin 24), (RubikOBTM.Band.slabPerm u b (RubikOBTM.Band.plus a d i) = RubikOBTM.Band.plus a d ((if d.val ≤ b.val then RubikOBTM.Band.actualSlabPlus else 1) i)) ∧ (RubikOBTM.Band.slabPerm u b (RubikOBTM.Band.minus a d i) = RubikOBTM.Band.minus a d ((if d.val ≤ b.val then RubikOBTM.Band.actualSlabMinus else 1) i)) :=
  @proof_RubikOBTM_Band_slab_action_if
