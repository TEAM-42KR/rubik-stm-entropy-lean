import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
import RubikSTM.Lemmas.OBTM.Compiler.GroupedCommutingProd
import RubikSTM.Lemmas.OBTM.Compiler.SlabCommute
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_cut_baseline_grouped {n : ℕ} {P : Type*} [DecidableEq P]
  (Y : Finset (Fin n)) (w : Fin n → P) (A : Finset P) (hw : ∀ d∈Y, w d∈A) :
  (A.toList.map (fun p => RubikOBTMCompiler.cutBaseline Y (Y.filter (fun d => w d=p)))).reverse.prod =
    RubikOBTMCompiler.fullBaseline Y := by
  classical
  by_cases hy : Y.Nonempty
  · have hh := RubikOBTMCompiler.grouped_commuting_prod Y
      (fun b => RubikOBTM.Band.slabPerm (Y.min' hy) b ^ 2)
      (fun b c => ((RubikOBTMCompiler.slab_commute (Y.min' hy) b c).pow_left 2).pow_right 2) w A hw
    simpa only [RubikOBTMCompiler.cutBaseline,RubikOBTMCompiler.fullBaseline,dif_pos hy] using hh
  · simp [RubikOBTMCompiler.cutBaseline,RubikOBTMCompiler.fullBaseline,hy]

#print axioms proof_RubikOBTMCompiler_cut_baseline_grouped
