import RubikSTM.Definitions.Bands.Band
import RubikSTM.Lemmas.Bands.SliceCoordinate
set_option autoImplicit false

theorem proof_RubikBand_sliceCommute {n : ℕ} (q : Rubik.Axis) (b c : Fin n) :
  Commute (Rubik.sliceQuarter n q b) (Rubik.sliceQuarter n q c) := by
  by_cases hbc : b = c
  · subst c; exact Commute.refl _
  have hcb : c ≠ b := Ne.symm hbc
  apply Equiv.ext
  intro s
  have hf : ∀ t : Rubik.Sticker n,
      Rubik.coordinate (Rubik.surfaceRotation n q t).val.1 q = Rubik.coordinate t.val.1 q := by
    intro t
    fin_cases q <;>
      simp [Rubik.surfaceRotation, Rubik.rawRotation, Rubik.coordinateRotation, Rubik.coordinate]
  change Rubik.sliceQuarter n q b (Rubik.sliceQuarter n q c s) =
    Rubik.sliceQuarter n q c (Rubik.sliceQuarter n q b s)
  by_cases hb : Rubik.coordinate s.val.1 q = b <;>
    by_cases hc : Rubik.coordinate s.val.1 q = c <;>
    simp [Rubik.sliceQuarter, hf, hb, hc, hbc, hcb]

#print axioms proof_RubikBand_sliceCommute
