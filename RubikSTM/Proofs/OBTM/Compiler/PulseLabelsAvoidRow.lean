import RubikSTM.Definitions.OBTM.Compiler.NativeProgram
import RubikSTM.Lemmas.Payloads.LabelOutsideThirdBand
import RubikSTM.Lemmas.Construction.Control.Physical.LabelsEqT
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_pulse_labels_avoid_row {n : ℕ} {a b c : Fin n} (hg : RubikGeometry.Generic n a b)
    (hc : RubikPayload.Half c) (hca : c ≠ a) (hcb : c ≠ b) (i : Fin 24) :
    ¬ RubikBand.Band c (RubikOBTM.Band.plus a b i) ∧
      ¬ RubikBand.Band c (RubikOBTM.Band.minus a b i) := by
  constructor
  · rw [RubikOBTM.Band.plus, RubikConstruction.Control.Physical.labels_eq_T]
    exact RubikPayload.labelOutsideThirdBand hg hc hca hcb i
  · rw [RubikOBTM.Band.minus, RubikConstruction.Control.Physical.labels_eq_T]
    have ha := hg.one_le_a
    have hb := hg.one_le_b
    have has := hg.a_small
    have hbs := hg.b_small
    have hc1 := hc.1
    have hcs := hc.2
    have hcaV : c.val ≠ a.val := by intro he; exact hca (Fin.ext he)
    have hcbV : c.val ≠ b.val := by intro he; exact hcb (Fin.ext he)
    fin_cases i <;>
      simp [RubikBand.Band, Fin.exists_fin_succ, Rubik.coordinate,
        RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
        RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev] <;> omega
