import RubikSTM.Proofs.OrbitGeometry.CommEltLab
import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
set_option autoImplicit false
open Rubik

theorem RubikGeometry.commElt_lab :
    ∀ {n : ℕ} {a b : Fin n} (hg : Generic n a b) (i : Fin 24), commElt a b (lab a b i) = lab a b (t0 i) :=
  @proof_RubikGeometry_commElt_lab
