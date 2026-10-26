import RubikSTM.Definitions.Orbits.SwapPhi
set_option autoImplicit false

theorem proof_RubikOrbit_labelBands {n : ℕ} (a b : Fin n) (i : Fin 24) :
  RubikBand.Band a (RubikGeometry.lab a b i) ∧ RubikBand.Band b (RubikGeometry.lab a b i) := by
  fin_cases i <;>
    simp [RubikBand.Band, Fin.exists_fin_succ, Rubik.coordinate,
      RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable] <;> tauto

#print axioms proof_RubikOrbit_labelBands
