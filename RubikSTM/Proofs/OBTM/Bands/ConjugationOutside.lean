import RubikSTM.Definitions.Bands.Band
import RubikSTM.Lemmas.Bands.WordBand
import RubikSTM.Definitions.Wings.SolverWord
import RubikSTM.Lemmas.OBTM.Bands.BaselineOutside
import RubikSTM.Lemmas.OBTM.Bands.BaselineBand
set_option autoImplicit false

theorem proof_RubikBand_conjugationOutside {n : ℕ} (a : Fin n) (w : List (Rubik.Move n))
  (hw : RubikBand.StrictControl a w) (q : Rubik.Axis) (Y : Finset (Fin n))
  (s : Rubik.Sticker n) (hs : ¬ (RubikBand.Band a s ∧ RubikBand.Bands Y s)) :
  (RubikBand.wordPerm w * RubikBand.parallelBaseline q Y * (RubikBand.wordPerm w)⁻¹) s =
    RubikBand.parallelBaseline q Y s := by
  let u := RubikBand.wordPerm w
  let Z := RubikBand.parallelBaseline q Y
  have cancel : u (u⁻¹ s) = s := Equiv.apply_symm_apply u s
  have hinv (b : Fin n) : RubikBand.Band b (u⁻¹ s) ↔ RubikBand.Band b s := by
    have h := RubikBand.wordBand b w (u⁻¹ s)
    simpa only [show RubikBand.wordPerm w = u from rfl, cancel] using h.symm
  change u (Z (u⁻¹ s)) = Z s
  by_cases ha : RubikBand.Band a s
  · have hb : ¬ RubikBand.Bands Y s := by intro h; exact hs ⟨ha, h⟩
    have hbi : ¬ RubikBand.Bands Y (u⁻¹ s) := by
      rintro ⟨b, hby, hbs⟩
      exact hb ⟨b, hby, (hinv b).mp hbs⟩
    have hz : Z (u⁻¹ s) = u⁻¹ s := RubikBand.baselineOutside q Y _ hbi
    have hzs : Z s = s := RubikBand.baselineOutside q Y s hb
    rw [hz, cancel, hzs]
  · have hu : u s = s := RubikBand.strictOutside a w hw s ha
    have hui : u⁻¹ s = s := by
      apply u.injective
      simpa only [cancel] using hu.symm
    have hza : ¬ RubikBand.Band a (Z s) := (RubikBand.baselineBand a q Y s).not.mpr ha
    have huz : u (Z s) = Z s := RubikBand.strictOutside a w hw _ hza
    rw [hui, huz]

#print axioms proof_RubikBand_conjugationOutside
