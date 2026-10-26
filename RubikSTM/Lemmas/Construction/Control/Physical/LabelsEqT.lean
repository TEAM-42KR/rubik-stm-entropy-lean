import RubikSTM.Proofs.Construction.Control.Physical.LabelsEqT
import Mathlib
import RubikSTM.Definitions.Construction.Control.K
import RubikSTM.Definitions.OrbitGeometry.GenPerm
set_option autoImplicit false

theorem RubikConstruction.Control.Physical.labels_eq_T :
    ∀ {n : ℕ} (a b : Fin n) (i : Fin 24), RubikConstruction.Control.lab a b i = RubikGeometry.lab a b i :=
  @proof_RubikConstruction_Control_Physical_labels_eq_T
