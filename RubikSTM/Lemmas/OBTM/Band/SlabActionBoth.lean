import RubikSTM.Proofs.OBTM.Band.SlabActionBoth
import RubikSTM.Definitions.OBTM.Band.SlabWord
set_option autoImplicit false

theorem RubikOBTM.Band.slab_action_both :
    ∀ {n : ℕ} (a u v : Fin n) (h : RubikOBTM.Band.Admissible n a u v) (d : Fin n) (hd : RubikOBTM.Band.InInterval u v d) (i : Fin 24), (RubikOBTM.Band.slabPerm u v (RubikOBTM.Band.plus a d i) = RubikOBTM.Band.plus a d (RubikOBTM.Band.actualSlabPlus i)) ∧ (RubikOBTM.Band.slabPerm u v (RubikOBTM.Band.minus a d i) = RubikOBTM.Band.minus a d (RubikOBTM.Band.actualSlabMinus i)) :=
  @proof_RubikOBTM_Band_slab_action_both
