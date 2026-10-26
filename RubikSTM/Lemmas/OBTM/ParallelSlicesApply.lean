import RubikSTM.Proofs.OBTM.ParallelSlicesApply
import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Lemmas.Bands.SliceCoordinate
set_option autoImplicit false

theorem RubikOBTM.parallel_slices_apply :
    ∀ {n : ℕ} (a : Rubik.Axis) (ls : List (Fin n)) (hl : ls.Nodup) (j : ℕ) (s : Rubik.Sticker n), ((ls.map (fun l => Rubik.sliceQuarter n a l ^ j)).reverse.prod) s = if Rubik.coordinate s.val.1 a ∈ ls then (Rubik.surfaceRotation n a ^ j) s else s :=
  @proof_RubikOBTM_parallel_slices_apply
