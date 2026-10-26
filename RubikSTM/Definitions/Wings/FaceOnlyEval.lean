import Mathlib
import RubikSTM.Definitions.Geometry.StmGraph
set_option autoImplicit false

namespace RubikWing
open Rubik
abbrev Label := Fin 24
abbrev Side := Fin 2
abbrev Alphabet := Sum (Fin 6) (Fin 6)
abbrev Word := FreeGroup Alphabet

def lo {n : ℕ} (c : Fin n) : Fin n := ⟨0, by have := c.isLt; omega⟩
def hi {n : ℕ} (c : Fin n) : Fin n := ⟨n-1, by have := c.isLt; omega⟩

structure Admissible (n : ℕ) (c : Fin n) : Prop where
  one_le : 1 ≤ c.val
  small : 2 * c.val + 2 ≤ n

def pos {n : ℕ} (c : Fin n) : Label → Coord n :=
  ![(lo c, lo c, c), (lo c, lo c, c.rev), (lo c, c, lo c), (lo c, c, hi c), (lo c, c.rev, lo c), (lo c, c.rev, hi c), (lo c, hi c, c), (lo c, hi c, c.rev), (c, lo c, lo c), (c, lo c, hi c), (c, hi c, lo c), (c, hi c, hi c), (c.rev, lo c, lo c), (c.rev, lo c, hi c), (c.rev, hi c, lo c), (c.rev, hi c, hi c), (hi c, lo c, c), (hi c, lo c, c.rev), (hi c, c, lo c), (hi c, c, hi c), (hi c, c.rev, lo c), (hi c, c.rev, hi c), (hi c, hi c, c), (hi c, hi c, c.rev)]

def normal : Label → Side → Normal :=
  ![![(0, false), (1, false)], ![(1, false), (0, false)], ![(2, false), (0, false)], ![(0, false), (2, true)], ![(0, false), (2, false)], ![(2, true), (0, false)], ![(1, true), (0, false)], ![(0, false), (1, true)], ![(1, false), (2, false)], ![(2, true), (1, false)], ![(2, false), (1, true)], ![(1, true), (2, true)], ![(2, false), (1, false)], ![(1, false), (2, true)], ![(1, true), (2, false)], ![(2, true), (1, true)], ![(1, false), (0, true)], ![(0, true), (1, false)], ![(0, true), (2, false)], ![(2, true), (0, true)], ![(2, false), (0, true)], ![(0, true), (2, true)], ![(0, true), (1, true)], ![(1, true), (0, true)]]

def lab {n : ℕ} (c : Fin n) (i : Label) (b : Side) : Sticker n :=
  ⟨(pos c i, normal i b), by
    fin_cases i <;> fin_cases b <;>
      simp [pos, normal, IsSurface, coordinate, lo, hi]⟩

def gen0 : Equiv.Perm Label where
  toFun := ![4, 2, 6, 0, 7, 1, 5, 3, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![3, 5, 1, 7, 0, 6, 2, 4, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def gen1 : Equiv.Perm Label where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 20, 18, 22, 16, 23, 17, 21, 19]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 19, 21, 17, 23, 16, 22, 18, 20]
  left_inv := by decide
  right_inv := by decide

def gen2 : Equiv.Perm Label where
  toFun := ![9, 13, 2, 3, 4, 5, 6, 7, 1, 17, 10, 11, 0, 16, 14, 15, 8, 12, 18, 19, 20, 21, 22, 23]
  invFun := ![12, 8, 2, 3, 4, 5, 6, 7, 16, 0, 10, 11, 17, 1, 14, 15, 13, 9, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def gen3 : Equiv.Perm Label where
  toFun := ![0, 1, 2, 3, 4, 5, 11, 15, 8, 9, 7, 23, 12, 13, 6, 22, 16, 17, 18, 19, 20, 21, 10, 14]
  invFun := ![0, 1, 2, 3, 4, 5, 14, 10, 8, 9, 22, 6, 12, 13, 23, 7, 16, 17, 18, 19, 20, 21, 15, 11]
  left_inv := by decide
  right_inv := by decide

def gen4 : Equiv.Perm Label where
  toFun := ![0, 1, 12, 3, 8, 5, 6, 7, 18, 9, 2, 11, 20, 13, 4, 15, 16, 17, 14, 19, 10, 21, 22, 23]
  invFun := ![0, 1, 10, 3, 14, 5, 6, 7, 4, 9, 20, 11, 2, 13, 18, 15, 16, 17, 8, 19, 12, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def gen5 : Equiv.Perm Label where
  toFun := ![0, 1, 2, 13, 4, 9, 6, 7, 8, 19, 10, 3, 12, 21, 14, 5, 16, 17, 18, 15, 20, 11, 22, 23]
  invFun := ![0, 1, 2, 11, 4, 15, 6, 7, 8, 5, 10, 21, 12, 3, 14, 19, 16, 17, 18, 9, 20, 13, 22, 23]
  left_inv := by decide
  right_inv := by decide

def gen6 : Equiv.Perm Label where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 10, 8, 11, 9, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 8, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def gen7 : Equiv.Perm Label where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 12, 15, 13, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 12, 14, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def gen8 : Equiv.Perm Label where
  toFun := ![0, 1, 3, 19, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 2, 18, 20, 21, 22, 23]
  invFun := ![0, 1, 18, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19, 3, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def gen9 : Equiv.Perm Label where
  toFun := ![0, 1, 2, 3, 5, 21, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 4, 20, 22, 23]
  invFun := ![0, 1, 2, 3, 20, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 5, 22, 23]
  left_inv := by decide
  right_inv := by decide

def gen10 : Equiv.Perm Label where
  toFun := ![16, 1, 2, 3, 4, 5, 0, 7, 8, 9, 10, 11, 12, 13, 14, 15, 22, 17, 18, 19, 20, 21, 6, 23]
  invFun := ![6, 1, 2, 3, 4, 5, 22, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 17, 18, 19, 20, 21, 16, 23]
  left_inv := by decide
  right_inv := by decide

def gen11 : Equiv.Perm Label where
  toFun := ![0, 17, 2, 3, 4, 5, 6, 1, 8, 9, 10, 11, 12, 13, 14, 15, 16, 23, 18, 19, 20, 21, 22, 7]
  invFun := ![0, 7, 2, 3, 4, 5, 6, 23, 8, 9, 10, 11, 12, 13, 14, 15, 16, 1, 18, 19, 20, 21, 22, 17]
  left_inv := by decide
  right_inv := by decide

def face : Fin 6 → Equiv.Perm Label := ![gen0, gen1, gen2, gen3, gen4, gen5]
def slice : Fin 6 → Equiv.Perm Label := ![gen6, gen7, gen8, gen9, gen10, gen11]

def finiteAtom : Alphabet → Equiv.Perm Label := Sum.elim face slice
def finiteEval : Word →* Equiv.Perm Label := FreeGroup.lift finiteAtom

def faceMove {n : ℕ} (c : Fin n) : Fin 6 → Move n :=
  ![(0, lo c, 0), (0, hi c, 0), (1, lo c, 0), (1, hi c, 0),
    (2, lo c, 0), (2, hi c, 0)]
def sliceMove {n : ℕ} (c : Fin n) : Fin 6 → Move n :=
  ![(0, c, 0), (0, c.rev, 0), (1, c, 0), (1, c.rev, 0),
    (2, c, 0), (2, c.rev, 0)]
def physicalAtom {n : ℕ} (c : Fin n) : Alphabet → Equiv.Perm (Sticker n) :=
  Sum.elim (fun i => movePermutation (faceMove c i))
    (fun i => movePermutation (sliceMove c i))
def physicalEval {n : ℕ} (c : Fin n) : Word →* Equiv.Perm (Sticker n) :=
  FreeGroup.lift (physicalAtom c)

def deletion : Word →* FreeGroup (Fin 6) :=
  FreeGroup.lift (Sum.elim FreeGroup.of (fun _ => 1))
def faceEval {n : ℕ} (c : Fin n) : FreeGroup (Fin 6) →* Equiv.Perm (Sticker n) :=
  FreeGroup.lift (fun i => movePermutation (faceMove c i))
def faceOnlyEval {n : ℕ} (c : Fin n) : Word →* Equiv.Perm (Sticker n) :=
  (faceEval c).comp deletion

end RubikWing
