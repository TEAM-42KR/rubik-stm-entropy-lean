import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
set_option autoImplicit false

theorem proof_RubikPayload_labelOutsideThirdBand {n : ℕ} {a b c : Fin n} (hg : RubikGeometry.Generic n a b)
  (hc : RubikPayload.Half c) (hca : c ≠ a) (hcb : c ≠ b) (i : Fin 24) :
  ¬ RubikBand.Band c (RubikGeometry.lab a b i) := by
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

#print axioms proof_RubikPayload_labelOutsideThirdBand
