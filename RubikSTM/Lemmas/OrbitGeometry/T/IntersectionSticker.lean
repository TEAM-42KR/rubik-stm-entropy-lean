import RubikSTM.Proofs.OrbitGeometry.T.IntersectionSticker
import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
set_option autoImplicit false
open Rubik

theorem RubikGeometry.T.intersection_sticker :
    ∀ {n : ℕ} {a b : Fin n} (hg : Generic n a b) (s : Sticker n)
    (hx : s.val.1.1 = a) (hy : s.val.1.2.1 = hi a) (hz : s.val.1.2.2 = b.rev), s = lab a b 4 :=
  @proof_RubikGeometry_T_intersection_sticker
