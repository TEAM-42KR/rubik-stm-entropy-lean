import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
import RubikSTM.Lemmas.Construction.Control.Physical.LabelsEqT
import RubikSTM.Lemmas.Orbits.FlipLabel
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_common_labels {n : ℕ} {a b : Fin n}
  (hg : RubikGeometry.Generic n a b) (hb : 0 < b.val ∧ b.val+1 < n) (i : Fin 24) :
  RubikOBTM.Band.plus a b i = RubikGeometry.lab a b i ∧
    RubikOBTM.Band.minus a b i = RubikOrbit.minusLab a b hb i := by
  constructor
  · exact RubikConstruction.Control.Physical.labels_eq_T a b i
  · rw [RubikOrbit.flipLabel hg hb]
    unfold RubikOBTM.Band.minus
    rw [RubikConstruction.Control.Physical.labels_eq_T]
    apply Subtype.ext
    fin_cases i <;> simp [RubikGeometry.lab,RubikGeometry.rawLab,RubikGeometry.posTable,RubikGeometry.normalTable,
      RubikGeometry.lo,RubikGeometry.hi,RubikOrbit.swapPhi]

#print axioms proof_RubikOBTMCompiler_common_labels
