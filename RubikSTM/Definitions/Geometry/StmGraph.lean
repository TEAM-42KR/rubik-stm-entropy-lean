import Mathlib
set_option autoImplicit false

namespace Rubik

abbrev Axis := Fin 3
abbrev Normal := Axis × Bool
abbrev Coord (n : ℕ) := Fin n × Fin n × Fin n
abbrev RawSticker (n : ℕ) := Coord n × Normal

def coordinate {n : ℕ} (p : Coord n) (a : Axis) : Fin n :=
  ![p.1, p.2.1, p.2.2] a

def IsSurface {n : ℕ} (s : RawSticker n) : Prop :=
  (coordinate s.1 s.2.1).val = if s.2.2 then n - 1 else 0

abbrev Sticker (n : ℕ) := {s : RawSticker n // IsSurface s}
abbrev Colour := Normal
abbrev Colouring (n : ℕ) := Sticker n → Colour

def solved (n : ℕ) : Colouring n := fun s => s.val.2

def coordinateRotation (n : ℕ) (a : Axis) : Equiv.Perm (Coord n) :=
  if a = 0 then
    { toFun := fun p => (p.1, p.2.2.rev, p.2.1)
      invFun := fun p => (p.1, p.2.2, p.2.1.rev)
      left_inv := by intro p; simp
      right_inv := by intro p; simp }
  else if a = 1 then
    { toFun := fun p => (p.2.2, p.2.1, p.1.rev)
      invFun := fun p => (p.2.2.rev, p.2.1, p.1)
      left_inv := by intro p; simp
      right_inv := by intro p; simp }
  else
    { toFun := fun p => (p.2.1.rev, p.1, p.2.2)
      invFun := fun p => (p.2.1, p.1.rev, p.2.2)
      left_inv := by intro p; simp
      right_inv := by intro p; simp }

def normalForward (a : Axis) (v : Normal) : Normal :=
  if a = 0 then ![(0, v.2), (2, v.2), (1, !v.2)] v.1
  else if a = 1 then ![(2, !v.2), (1, v.2), (0, v.2)] v.1
  else ![(1, v.2), (0, !v.2), (2, v.2)] v.1

def normalBackward (a : Axis) (v : Normal) : Normal :=
  if a = 0 then ![(0, v.2), (2, !v.2), (1, v.2)] v.1
  else if a = 1 then ![(2, v.2), (1, v.2), (0, !v.2)] v.1
  else ![(1, !v.2), (0, v.2), (2, v.2)] v.1

def normalRotation (a : Axis) : Equiv.Perm Normal where
  toFun := normalForward a
  invFun := normalBackward a
  left_inv := by
    rintro ⟨b, c⟩
    fin_cases a <;> fin_cases b <;> cases c <;> rfl
  right_inv := by
    rintro ⟨b, c⟩
    fin_cases a <;> fin_cases b <;> cases c <;> rfl

def rawRotation (n : ℕ) (a : Axis) : Equiv.Perm (RawSticker n) :=
  (coordinateRotation n a).prodCongr (normalRotation a)

def surfaceRotation (n : ℕ) (a : Axis) : Equiv.Perm (Sticker n) :=
  (rawRotation n a).subtypeEquiv (by
    rintro ⟨⟨x, y, z⟩, b, c⟩
    fin_cases a <;> fin_cases b <;> cases c <;>
      simp [IsSurface, rawRotation, coordinateRotation, normalRotation,
        normalForward, coordinate, Fin.rev] <;>
      omega)

def sliceQuarter (n : ℕ) (a : Axis) (layer : Fin n) : Equiv.Perm (Sticker n) where
  toFun := fun s => if coordinate s.val.1 a = layer then surfaceRotation n a s else s
  invFun := fun s => if coordinate s.val.1 a = layer then (surfaceRotation n a).symm s else s
  left_inv := by
    intro s
    have hf : ∀ t : Sticker n,
        coordinate (surfaceRotation n a t).val.1 a = coordinate t.val.1 a := by
      intro t
      fin_cases a <;> simp [surfaceRotation, rawRotation, coordinateRotation, coordinate]
    have hb : ∀ t : Sticker n,
        coordinate ((surfaceRotation n a).symm t).val.1 a = coordinate t.val.1 a := by
      intro t
      simpa only [Equiv.apply_symm_apply] using (hf ((surfaceRotation n a).symm t)).symm
    by_cases h : coordinate s.val.1 a = layer
    · simp [h, hf]
    · simp [h]
  right_inv := by
    intro s
    have hf : ∀ t : Sticker n,
        coordinate (surfaceRotation n a t).val.1 a = coordinate t.val.1 a := by
      intro t
      fin_cases a <;> simp [surfaceRotation, rawRotation, coordinateRotation, coordinate]
    have hb : ∀ t : Sticker n,
        coordinate ((surfaceRotation n a).symm t).val.1 a = coordinate t.val.1 a := by
      intro t
      simpa only [Equiv.apply_symm_apply] using (hf ((surfaceRotation n a).symm t)).symm
    by_cases h : coordinate s.val.1 a = layer
    · simp [h, hb]
    · simp [h]

abbrev Move (n : ℕ) := Axis × Fin n × Fin 3

def movePermutation {n : ℕ} (m : Move n) : Equiv.Perm (Sticker n) :=
  (sliceQuarter n m.1 m.2.1) ^ (m.2.2.val + 1)

def applyMove {n : ℕ} (m : Move n) (c : Colouring n) : Colouring n :=
  fun s => c ((movePermutation m).symm s)

def applyWord {n : ℕ} (w : List (Move n)) (c : Colouring n) : Colouring n :=
  w.foldl (fun state m => applyMove m state) c

end Rubik

namespace Rubik

def Reachable {n : ℕ} (c : Colouring n) : Prop :=
  ∃ w : List (Move n), applyWord w (solved n) = c

abbrev Position (n : ℕ) := {c : Colouring n // Reachable c}

noncomputable instance positionFintype (n : ℕ) : Fintype (Position n) := Fintype.ofFinite _

def stmGraph (n : ℕ) : SimpleGraph (Position n) where
  Adj c d := c ≠ d ∧
    ((∃ m : Move n, applyMove m c.val = d.val) ∨
      (∃ m : Move n, applyMove m d.val = c.val))
  symm := ⟨by
    intro c d h
    exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro c h; exact h.1 rfl⟩

noncomputable def diameter (n : ℕ) : ℕ := (stmGraph n).diam

noncomputable def entropyConstant : ℝ :=
  (1 / 4 : ℝ) * Real.log ((Nat.factorial 24 : ℝ) / (Nat.factorial 4 : ℝ) ^ 6)

noncomputable def normalizedDiameter (n : ℕ) : ℝ :=
  (diameter n : ℝ) * Real.log (n : ℝ) / (n : ℝ) ^ 2

end Rubik
