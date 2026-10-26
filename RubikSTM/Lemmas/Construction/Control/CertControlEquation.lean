import RubikSTM.Proofs.Construction.Control.CertControlEquation
import Mathlib
import RubikSTM.Definitions.Construction.Control.K
set_option autoImplicit false

theorem RubikConstruction.Control.cert_control_equation :
    ∀ (i : RubikConstruction.Control.CertIndex), RubikConstruction.Control.certPerm i = if RubikConstruction.Control.certPositive i then RubikConstruction.Control.control (RubikConstruction.Control.certControlIndex i) else (RubikConstruction.Control.control (RubikConstruction.Control.certControlIndex i))⁻¹ :=
  @proof_RubikConstruction_Control_cert_control_equation
