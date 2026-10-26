import RubikSTM.Definitions.Bands.Band
set_option autoImplicit false

theorem proof_RubikBand_sliceCoordinate {n : ℕ} (q : Rubik.Axis) (l : Fin n) (s : Rubik.Sticker n) :
  Rubik.coordinate (Rubik.sliceQuarter n q l s).val.1 q = Rubik.coordinate s.val.1 q := by
  have hf : Rubik.coordinate (Rubik.surfaceRotation n q s).val.1 q =
      Rubik.coordinate s.val.1 q := by
    fin_cases q <;>
      simp [Rubik.surfaceRotation, Rubik.rawRotation, Rubik.coordinateRotation, Rubik.coordinate]
  by_cases h : Rubik.coordinate s.val.1 q = l <;> simp [Rubik.sliceQuarter, h, hf]

#print axioms proof_RubikBand_sliceCoordinate
