import RubikSTM.Definitions.Geometry.StmGraph
import RubikSTM.Definitions.OrbitGeometry.NormalTable
set_option autoImplicit false

namespace RubikGeometry
open Rubik

def moveGroup (n : ℕ) : Subgroup (Equiv.Perm (Sticker n)) :=
  Subgroup.closure (Set.range (fun m : Move n => movePermutation m))

section Labels
variable {n : ℕ}

def lo (a : Fin n) : Fin n := ⟨0, by have := a.isLt; omega⟩

def hi (a : Fin n) : Fin n := ⟨n - 1, by have := a.isLt; omega⟩

structure Generic (n : ℕ) (a b : Fin n) : Prop where
  one_le_a : 1 ≤ a.val
  one_le_b : 1 ≤ b.val
  a_small : 2 * a.val + 2 ≤ n
  b_small : 2 * b.val + 2 ≤ n
  ne : a ≠ b

def posTable (a b : Fin n) : Fin 24 → Coord n :=
  ![(hi a, b.rev, a),
    (hi a, b, a.rev),
    (hi a, a.rev, b.rev),
    (hi a, a, b),
    (a, hi a, b.rev),
    (a, b, hi a),
    (b.rev, a, hi a),
    (a.rev, b.rev, hi a),
    (b, a.rev, hi a),
    (b, lo a, a.rev),
    (lo a, b.rev, a.rev),
    (lo a, b, a),
    (b.rev, hi a, a.rev),
    (a.rev, hi a, b),
    (b, hi a, a),
    (lo a, a, b.rev),
    (lo a, a.rev, b),
    (a.rev, lo a, b.rev),
    (b.rev, lo a, a),
    (a, lo a, b),
    (b, a, lo a),
    (a.rev, b, lo a),
    (b.rev, a.rev, lo a),
    (a, b.rev, lo a)]

def rawLab (a b : Fin n) (i : Fin 24) : RawSticker n := (posTable a b i, normalTable i)

theorem rawLab_isSurface (a b : Fin n) (i : Fin 24) : IsSurface (rawLab a b i) := by
  fin_cases i <;> simp [rawLab, posTable, normalTable, IsSurface, coordinate, lo, hi]

def lab (a b : Fin n) (i : Fin 24) : Sticker n := ⟨rawLab a b i, rawLab_isSurface a b i⟩

def genMove (a b : Fin n) : Fin 8 → Move n :=
  ![(0, lo a, 0), (0, hi a, 0), (1, lo a, 0), (1, hi a, 0), (2, lo a, 0), (2, hi a, 0), (0, a, 0),
    (2, b.rev, 0)]

end Labels

def gen0 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 12, 13, 14, 11, 10, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 16, 15, 12, 13, 14, 10, 11, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def gen1 : Equiv.Perm (Fin 24) where
  toFun := ![2, 3, 1, 0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![3, 2, 0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def gen2 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 17, 10, 11, 12, 13, 14, 15, 16, 18, 19, 9, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 19, 10, 11, 12, 13, 14, 15, 16, 9, 17, 18, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def gen3 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 12, 5, 6, 7, 8, 9, 10, 11, 13, 14, 4, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 14, 5, 6, 7, 8, 9, 10, 11, 4, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def gen4 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 20]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 23, 20, 21, 22]
  left_inv := by decide
  right_inv := by decide

def gen5 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 6, 7, 8, 5, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 4, 8, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def gen6 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 5, 19, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 23, 20, 21, 22, 4]
  invFun := ![0, 1, 2, 3, 23, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 5, 20, 21, 22, 19]
  left_inv := by decide
  right_inv := by decide

def gen7 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 4, 3, 15, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 17, 16, 2, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 17, 3, 2, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 4, 16, 15, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def genPerm : Fin 8 → Equiv.Perm (Fin 24) := ![gen0, gen1, gen2, gen3, gen4, gen5, gen6, gen7]

def commElt {n : ℕ} (a b : Fin n) : Equiv.Perm (Sticker n) :=
  let P := (movePermutation (genMove a b 6))⁻¹ * movePermutation (genMove a b 5) *
      movePermutation (genMove a b 6)
  let Q := movePermutation (genMove a b 7)
  P * Q * P⁻¹ * Q⁻¹

def t0 : Equiv.Perm (Fin 24) :=
  let P := (genPerm 6)⁻¹ * genPerm 5 * genPerm 6
  let Q := genPerm 7
  P * Q * P⁻¹ * Q⁻¹

def orbitGroup {n : ℕ} (a b : Fin n) : Subgroup (Equiv.Perm (Fin 24)) where
  carrier := {τ | ∃ g ∈ moveGroup n, (∀ i, g (lab a b i) = lab a b (τ i)) ∧
      ∀ s, s ∉ Set.range (lab a b) → g s = s}
  one_mem' := ⟨1, Subgroup.one_mem _, by simp, by simp⟩
  mul_mem' := by
    rintro τ₁ τ₂ ⟨g₁, hg₁, h₁, k₁⟩ ⟨g₂, hg₂, h₂, k₂⟩
    refine ⟨g₁ * g₂, Subgroup.mul_mem _ hg₁ hg₂, ?_, ?_⟩
    · intro i; simp [h₁, h₂]
    · intro s hs; simp [k₂ s hs, k₁ s hs]
  inv_mem' := by
    rintro τ ⟨g, hg, h, k⟩
    refine ⟨g⁻¹, Subgroup.inv_mem _ hg, ?_, ?_⟩
    · intro i
      rw [Equiv.Perm.inv_eq_iff_eq, h]; simp
    · intro s hs
      rw [Equiv.Perm.inv_eq_iff_eq, k s hs]

def orbitColourings : ℕ := Nat.factorial 24 / (Nat.factorial 4) ^ 6

end RubikGeometry
