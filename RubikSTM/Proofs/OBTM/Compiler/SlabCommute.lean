import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
import RubikSTM.Lemmas.OBTM.Band.SlabPermApply
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_slab_commute {n : ℕ} (u v w : Fin n) :
  Commute (RubikOBTM.Band.slabPerm u v) (RubikOBTM.Band.slabPerm u w) := by
  have hf (s : Rubik.Sticker n) :
      Rubik.coordinate (Rubik.surfaceRotation n 2 s).val.1 2 = Rubik.coordinate s.val.1 2 := by
    simp [Rubik.surfaceRotation,Rubik.rawRotation,Rubik.coordinateRotation,Rubik.coordinate]
  apply Equiv.ext
  intro s
  change RubikOBTM.Band.slabPerm u v (RubikOBTM.Band.slabPerm u w s) =
    RubikOBTM.Band.slabPerm u w (RubikOBTM.Band.slabPerm u v s)
  by_cases hv : RubikOBTM.Band.InInterval u v (Rubik.coordinate s.val.1 2).rev <;>
    by_cases hw : RubikOBTM.Band.InInterval u w (Rubik.coordinate s.val.1 2).rev <;>
    simp [RubikOBTM.Band.slab_perm_apply,hf,hv,hw]

#print axioms proof_RubikOBTMCompiler_slab_commute
