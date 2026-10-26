import RubikSTM.Definitions.Geometry.StmGraph
set_option autoImplicit false

namespace RubikIntertwiner

def coordinateFlip {n : ℕ} (b : Fin n) : Equiv.Perm (Rubik.Coord n) :=
  (Equiv.swap b b.rev).prodCongr ((Equiv.swap b b.rev).prodCongr (Equiv.swap b b.rev))

def rawFlip {n : ℕ} (b : Fin n) : Equiv.Perm (Rubik.RawSticker n) :=
  (coordinateFlip b).prodCongr (Equiv.refl Rubik.Normal)

def surfaceFlip {n : ℕ} (b : Fin n) (hb : 0 < b.val ∧ b.val + 1 < n) :
    Equiv.Perm (Rubik.Sticker n) :=
  (rawFlip b).subtypeEquiv (by
    rintro ⟨⟨x,y,z⟩,a,c⟩
    have hbr : 0 < b.rev.val ∧ b.rev.val + 1 < n := by
      simp only [Fin.rev]
      omega
    fin_cases a <;> cases c <;>
      simp [Rubik.IsSurface, rawFlip, coordinateFlip, Rubik.coordinate, Equiv.swap_apply_def] <;>
      split_ifs <;> simp_all <;> omega)

end RubikIntertwiner
