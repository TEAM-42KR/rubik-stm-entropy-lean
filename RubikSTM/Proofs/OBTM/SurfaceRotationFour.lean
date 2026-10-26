import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Lemmas.OBTM.ParallelSlicesApply
import RubikSTM.Definitions.Wings.SolverWord
set_option autoImplicit false

theorem proof_RubikOBTM_surfaceRotation_four (n : ℕ) (a : Rubik.Axis) : Rubik.surfaceRotation n a ^ 4 = 1 := by
  apply Equiv.ext
  intro s
  have h := RubikOBTM.parallel_slices_apply a [Rubik.coordinate s.val.1 a] (by simp) 4 s
  simpa [Rubik.sliceQuarter_order_four] using h.symm
