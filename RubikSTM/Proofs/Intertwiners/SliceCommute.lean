import RubikSTM.Definitions.Intertwiners.SurfaceFlip
set_option autoImplicit false
open RubikIntertwiner

private theorem RubikIntertwiner.flip_rev {n : ℕ} (b x : Fin n) :
    Equiv.swap b b.rev x.rev = (Equiv.swap b b.rev x).rev := by
  simpa only [Fin.revPerm_apply, Fin.rev_rev, Equiv.swap_comm] using
    (Function.Injective.map_swap (Fin.revPerm : Equiv.Perm (Fin n)).injective b b.rev x).symm

private theorem RubikIntertwiner.raw_rotation {n : ℕ} (b : Fin n) (a : Rubik.Axis) :
    rawFlip b * Rubik.rawRotation n a = Rubik.rawRotation n a * rawFlip b := by
  apply Equiv.ext
  rintro ⟨⟨x,y,z⟩,v⟩
  fin_cases a <;>
    simp [rawFlip, coordinateFlip, Rubik.rawRotation, Rubik.coordinateRotation, flip_rev]

private theorem RubikIntertwiner.slice_transport {n : ℕ} (b : Fin n)
    (hb : 0 < b.val ∧ b.val + 1 < n) (a : Rubik.Axis) (l : Fin n) :
    surfaceFlip b hb * Rubik.sliceQuarter n a l =
      Rubik.sliceQuarter n a (Equiv.swap b b.rev l) * surfaceFlip b hb := by
  let F := surfaceFlip b hb
  let q := Rubik.surfaceRotation n a
  have hcoord (s : Rubik.Sticker n) :
      Rubik.coordinate (F s).val.1 a = Equiv.swap b b.rev (Rubik.coordinate s.val.1 a) := by
    fin_cases a <;> simp [F, surfaceFlip, rawFlip, coordinateFlip, Rubik.coordinate]
  have hrot (s : Rubik.Sticker n) : F (q s) = q (F s) := by
    apply Subtype.ext
    exact congrArg (fun e : Equiv.Perm (Rubik.RawSticker n) => e s.val) (raw_rotation b a)
  apply Equiv.ext
  intro s
  change F (Rubik.sliceQuarter n a l s) =
    Rubik.sliceQuarter n a (Equiv.swap b b.rev l) (F s)
  have heq : Rubik.coordinate (F s).val.1 a = Equiv.swap b b.rev l ↔
      Rubik.coordinate s.val.1 a = l := by
    rw [hcoord]
    exact (Equiv.swap b b.rev).injective.eq_iff
  by_cases h : Rubik.coordinate s.val.1 a = l
  · simpa only [Rubik.sliceQuarter, Equiv.coe_fn_mk, h, if_true,
      heq.mpr h] using hrot s
  · simp only [Rubik.sliceQuarter, Equiv.coe_fn_mk, h, if_false,
      (not_congr heq).mpr h]

theorem proof_RubikIntertwiner_slice_commute {n : ℕ} (b : Fin n)
    (hb : 0 < b.val ∧ b.val + 1 < n) (a : Rubik.Axis) (l : Fin n)
    (h₁ : l ≠ b) (h₂ : l ≠ b.rev) :
    Commute (surfaceFlip b hb) (Rubik.sliceQuarter n a l) := by
  show surfaceFlip b hb * Rubik.sliceQuarter n a l =
    Rubik.sliceQuarter n a l * surfaceFlip b hb
  simpa only [Equiv.swap_apply_of_ne_of_ne h₁ h₂] using slice_transport b hb a l
