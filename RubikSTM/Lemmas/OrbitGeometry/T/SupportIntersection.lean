import RubikSTM.Proofs.OrbitGeometry.T.SupportIntersection
import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
set_option autoImplicit false
open Rubik

theorem RubikGeometry.T.support_intersection :
    ∀ {n : ℕ} {a b : Fin n} (hg : Generic n a b) (s : Sticker n)
    (hp : ((movePermutation (genMove a b 6))⁻¹ * movePermutation (genMove a b 5) *
      movePermutation (genMove a b 6)) s ≠ s)
    (hq : movePermutation (genMove a b 7) s ≠ s), s ∈ Set.range (lab a b) :=
  @proof_RubikGeometry_T_support_intersection
