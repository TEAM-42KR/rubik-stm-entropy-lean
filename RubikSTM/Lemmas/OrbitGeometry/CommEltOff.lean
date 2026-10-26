import RubikSTM.Proofs.OrbitGeometry.CommEltOff
import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
set_option autoImplicit false
open Rubik

theorem RubikGeometry.commElt_off :
    ∀ {n : ℕ} {a b : Fin n} (hg : Generic n a b) (s : Sticker n)
    (hs : s ∉ Set.range (lab a b)), commElt a b s = s :=
  @proof_RubikGeometry_commElt_off
