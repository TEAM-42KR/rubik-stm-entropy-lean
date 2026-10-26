import RubikSTM.Proofs.OBTM.Band.SlabPermApply
import RubikSTM.Definitions.OBTM.Band.SlabWord
set_option autoImplicit false
open scoped Classical

theorem RubikOBTM.Band.slab_perm_apply :
    ∀ {n : ℕ} (u v : Fin n) (s : Rubik.Sticker n), RubikOBTM.Band.slabPerm u v s = if RubikOBTM.Band.InInterval u v (Rubik.coordinate s.val.1 2).rev then Rubik.surfaceRotation n 2 s else s :=
  @proof_RubikOBTM_Band_slab_perm_apply
