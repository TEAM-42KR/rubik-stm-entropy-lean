import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Definitions.LocalActions.Generic.ModelEval
import RubikSTM.Lemmas.OrbitGeometry.F.ThreeT0
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open Rubik RubikGeometry
open RubikLocal.Generic RubikConstruction.Control.Physical
theorem proof_RubikLocal_Generic_alternating_range : alternatingGroup (Fin 24) ≤ modelEval.range := by
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
  apply (Subgroup.closure_le _).mpr
  intro c hc
  have hj : IsConj RubikGeometry.t0 c :=
    Equiv.Perm.isConj_iff_cycleType_eq.mpr (RubikGeometry.F.three_t0.trans hc.symm)
  obtain ⟨q, hq⟩ := isConj_iff.mp hj
  refine ⟨FreeGroup.of q, ?_⟩
  simpa [modelEval, conjugateThree] using hq
