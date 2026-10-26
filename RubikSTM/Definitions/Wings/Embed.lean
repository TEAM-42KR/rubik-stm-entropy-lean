import RubikSTM.Definitions.Wings.FaceOnlyEval
set_option autoImplicit false

namespace RubikWing
open Rubik

def level {n : ℕ} (c : Fin n) : Fin 4 → Fin n := ![lo c, c, c.rev, hi c]
def embedPos {n : ℕ} (c : Fin n) (p : Coord 4) : Coord n :=
  (level c p.1, level c p.2.1, level c p.2.2)

def embed {n : ℕ} (c : Fin n) (s : Sticker 4) : Sticker n :=
  ⟨(embedPos c s.val.1, s.val.2), by
    have hcoord : coordinate (embedPos c s.val.1) s.val.2.1 =
        level c (coordinate s.val.1 s.val.2.1) := by
      generalize s.val.2.1 = a
      fin_cases a <;> rfl
    change (coordinate (embedPos c s.val.1) s.val.2.1).val = _
    rw [hcoord]
    have hs : coordinate s.val.1 s.val.2.1 =
        (if s.val.2.2 then (3 : Fin 4) else 0) := by
      cases hb : s.val.2.2 <;> apply Fin.ext <;>
        simpa [IsSurface, hb] using s.property
    rw [hs]
    cases s.val.2.2 <;> rfl⟩

end RubikWing
