import RubikSTM.Proofs.Orbits.LabelBands
import RubikSTM.Definitions.Orbits.SwapPhi
set_option autoImplicit false

theorem RubikOrbit.labelBands :
    ∀ {n : ℕ} (a b : Fin n) (i : Fin 24), RubikBand.Band a (RubikGeometry.lab a b i) ∧ RubikBand.Band b (RubikGeometry.lab a b i) :=
  @proof_RubikOrbit_labelBands
