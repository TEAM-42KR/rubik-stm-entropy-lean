import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Lemmas.OBTM.ParallelSlicesApply
import RubikSTM.Lemmas.OBTM.BlockPowerApply
set_option autoImplicit false

theorem proof_RubikOBTM_blockSliceWord_permutation {n : ℕ} (m : RubikOBTM.BlockMove n) :
    (((RubikOBTM.blockSliceWord m).map Rubik.movePermutation).reverse.prod) =
      RubikOBTM.blockPermutation m := by
  apply Equiv.ext
  intro s
  let ls := (List.finRange n).filter (fun l => RubikOBTM.selected m.1 m.2.1 m.2.2.1 l)
  have hnodup : ls.Nodup := (List.nodup_finRange n).filter _
  have hp := RubikOBTM.parallel_slices_apply m.1 ls hnodup (m.2.2.2.val + 1) s
  change (((ls.map (fun l => (m.1, l, m.2.2.2))).map Rubik.movePermutation).reverse.prod) s = _
  simp only [List.map_map, Function.comp_def]
  change ((ls.map (fun l => Rubik.sliceQuarter n m.1 l ^ (m.2.2.2.val + 1))).reverse.prod) s = _
  rw [hp, RubikOBTM.blockPermutation, RubikOBTM.block_power_apply]
  simp [ls]
