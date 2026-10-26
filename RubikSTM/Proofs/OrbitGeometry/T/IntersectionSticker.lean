import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open Rubik RubikGeometry
theorem proof_RubikGeometry_T_intersection_sticker {n : ℕ} {a b : Fin n} (hg : Generic n a b) (s : Sticker n)
    (hx : s.val.1.1 = a) (hy : s.val.1.2.1 = hi a) (hz : s.val.1.2.2 = b.rev) :
    s = lab a b 4 := by
  have ha := hg.one_le_a
  have hb := hg.one_le_b
  have has := hg.a_small
  have hbs := hg.b_small
  rcases s with ⟨⟨⟨x,y,z⟩,v,c⟩,hs⟩
  dsimp only at hx hy hz
  subst x; subst y; subst z
  apply Subtype.ext
  fin_cases v <;> cases c <;>
    simp [IsSurface, coordinate, hi, Fin.rev] at hs <;>
    simp [lab, rawLab, posTable, normalTable] <;> omega
