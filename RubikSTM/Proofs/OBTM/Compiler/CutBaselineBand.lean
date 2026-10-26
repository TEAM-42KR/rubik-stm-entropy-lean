import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
import RubikSTM.Lemmas.OBTM.Band.SlabPermApply
import RubikSTM.Definitions.Wings.SolverWord
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_cut_baseline_band {n : ℕ} (Y B : Finset (Fin n))
  (a : Fin n) (s : Rubik.Sticker n) :
  RubikBand.Band a (RubikOBTMCompiler.cutBaseline Y B s) ↔ RubikBand.Band a s := by
  classical
  by_cases hy : Y.Nonempty
  · let u := Y.min' hy
    have hs (b : Fin n) (x : Rubik.Sticker n) :
        RubikBand.Band a (RubikOBTM.Band.slabPerm u b x) ↔ RubikBand.Band a x := by
      rw [RubikOBTM.Band.slab_perm_apply]
      split_ifs
      · exact RubikBand.rotationBand a 2 x
      · rfl
    have hs2 (b : Fin n) (x : Rubik.Sticker n) :
        RubikBand.Band a (((RubikOBTM.Band.slabPerm u b)^2) x) ↔ RubikBand.Band a x := by
      rw [pow_two,Equiv.Perm.mul_apply]
      exact (hs b _).trans (hs b _)
    have hl (bs : List (Fin n)) (x : Rubik.Sticker n) :
        RubikBand.Band a ((bs.map (fun b => RubikOBTM.Band.slabPerm u b^2)).reverse.prod x) ↔
          RubikBand.Band a x := by
      induction bs generalizing x with
      | nil => rfl
      | cons b bs ih =>
        simp only [List.map_cons,List.reverse_cons,List.prod_append,List.prod_singleton,Equiv.Perm.mul_apply]
        exact (ih _).trans (hs2 b x)
    simpa only [RubikOBTMCompiler.cutBaseline,dif_pos hy,u] using hl B.toList s
  · simp [RubikOBTMCompiler.cutBaseline,hy]

#print axioms proof_RubikOBTMCompiler_cut_baseline_band
