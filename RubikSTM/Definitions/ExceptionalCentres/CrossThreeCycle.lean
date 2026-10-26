import RubikSTM.Definitions.ExceptionalCentres.WordPerm
set_option autoImplicit false

namespace RubikExceptional
open Rubik RubikGeometry

def crossGen0 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 12, 13, 14, 11, 10, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 16, 15, 12, 13, 14, 10, 11, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def crossGen1 : Equiv.Perm (Fin 24) where
  toFun := ![2, 3, 1, 0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![3, 2, 0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def crossGen2 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 17, 10, 11, 12, 13, 14, 15, 16, 18, 19, 9, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 19, 10, 11, 12, 13, 14, 15, 16, 9, 17, 18, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def crossGen3 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 12, 5, 6, 7, 8, 9, 10, 11, 13, 14, 4, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 14, 5, 6, 7, 8, 9, 10, 11, 4, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def crossGen4 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 20]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 23, 20, 21, 22]
  left_inv := by decide
  right_inv := by decide

def crossGen5 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 6, 7, 8, 5, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 4, 8, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def crossGen6 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 5, 19, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 23, 20, 21, 22, 4]
  invFun := ![0, 1, 2, 3, 23, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 5, 20, 21, 22, 19]
  left_inv := by decide
  right_inv := by decide

def crossGen7 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 4, 13, 15, 5, 6, 7, 8, 9, 10, 11, 12, 16, 14, 17, 19, 2, 18, 3, 20, 21, 22, 23]
  invFun := ![0, 1, 17, 19, 2, 5, 6, 7, 8, 9, 10, 11, 12, 3, 14, 4, 13, 15, 18, 16, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def crossGen : Fin 8 → Equiv.Perm (Fin 24) := ![crossGen0, crossGen1, crossGen2, crossGen3, crossGen4, crossGen5, crossGen6, crossGen7]

def crossControlGen0 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 12, 13, 14, 11, 10, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 16, 15, 12, 13, 14, 10, 11, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def crossControlGen1 : Equiv.Perm (Fin 24) where
  toFun := ![2, 3, 1, 0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![3, 2, 0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def crossControlGen2 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 17, 10, 11, 12, 13, 14, 15, 16, 18, 19, 9, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 19, 10, 11, 12, 13, 14, 15, 16, 9, 17, 18, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def crossControlGen3 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 12, 5, 6, 7, 8, 9, 10, 11, 13, 14, 4, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 14, 5, 6, 7, 8, 9, 10, 11, 4, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def crossControlGen4 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 20]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 23, 20, 21, 22]
  left_inv := by decide
  right_inv := by decide

def crossControlGen5 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 6, 7, 8, 5, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 4, 8, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def crossControlGen6 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 5, 19, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 23, 20, 21, 22, 4]
  invFun := ![0, 1, 2, 3, 23, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 5, 20, 21, 22, 19]
  left_inv := by decide
  right_inv := by decide

def crossControlGen7 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 20, 4, 5, 3, 7, 8, 9, 10, 11, 12, 13, 14, 6, 16, 17, 18, 19, 15, 21, 22, 23]
  invFun := ![0, 1, 2, 6, 4, 5, 15, 7, 8, 9, 10, 11, 12, 13, 14, 20, 16, 17, 18, 19, 3, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def crossControlGen8 : Equiv.Perm (Fin 24) where
  toFun := ![14, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 18, 12, 13, 11, 15, 16, 17, 0, 19, 20, 21, 22, 23]
  invFun := ![18, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 14, 12, 13, 0, 15, 16, 17, 11, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def crossControl : Fin 9 → Equiv.Perm (Fin 24) := ![crossControlGen0, crossControlGen1, crossControlGen2, crossControlGen3, crossControlGen4, crossControlGen5, crossControlGen6, crossControlGen7, crossControlGen8]

def crossControlMove {n : ℕ} (a : Fin n) : Fin 9 → Move n :=
  ![(0,lo a,0),(0,hi a,0),(1,lo a,0),(1,hi a,0),(2,lo a,0),(2,hi a,0),
    (0,a,0),(1,a,0),(2,a,0)]

def crossThreeCycle : Equiv.Perm (Fin 24) :=
  let P := (crossGen 6)⁻¹ * crossGen 5 * crossGen 6
  let Q := crossGen 7
  P * Q * P⁻¹ * Q⁻¹

def CrossSolves {n : ℕ} (a b : Fin n) (τ : Equiv.Perm (Fin 24))
    (w : List (Move n)) : Prop :=
  (∀ i, wordPerm w (lab a b i) = lab a b (τ i)) ∧
  ∀ s, s ∉ Set.range (lab a b) → wordPerm w s = s

end RubikExceptional
