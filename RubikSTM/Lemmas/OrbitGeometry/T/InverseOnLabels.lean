import RubikSTM.Proofs.OrbitGeometry.T.InverseOnLabels
import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
set_option autoImplicit false
open Rubik

theorem RubikGeometry.T.inverse_on_labels :
    ∀ {α β : Type*} (f : β → α) (p : Equiv.Perm α) (q : Equiv.Perm β)
    (h : ∀ i, p (f i) = f (q i)) (i : β), p⁻¹ (f i) = f (q⁻¹ i) :=
  @proof_RubikGeometry_T_inverse_on_labels
