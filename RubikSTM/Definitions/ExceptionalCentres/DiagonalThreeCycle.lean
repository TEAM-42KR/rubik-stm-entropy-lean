import RubikSTM.Definitions.OrbitGeometry.GenPerm
set_option autoImplicit false

namespace RubikExceptional
open Rubik RubikGeometry

structure Regular (n : ℕ) (a : Fin n) : Prop where
  positive : 1 ≤ a.val
  small : 2 * a.val + 2 ≤ n

def diagGen0 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 12, 13, 14, 11, 10, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 16, 15, 12, 13, 14, 10, 11, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def diagGen1 : Equiv.Perm (Fin 24) where
  toFun := ![2, 3, 1, 0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![3, 2, 0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def diagGen2 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 17, 10, 11, 12, 13, 14, 15, 16, 18, 19, 9, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 19, 10, 11, 12, 13, 14, 15, 16, 9, 17, 18, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def diagGen3 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 12, 5, 6, 7, 8, 9, 10, 11, 13, 14, 4, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 14, 5, 6, 7, 8, 9, 10, 11, 4, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def diagGen4 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 20]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 23, 20, 21, 22]
  left_inv := by decide
  right_inv := by decide

def diagGen5 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 6, 7, 8, 5, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 4, 8, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def diagGen6 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 5, 19, 6, 7, 9, 20, 10, 11, 12, 13, 8, 15, 16, 17, 18, 23, 14, 21, 22, 4]
  invFun := ![0, 1, 2, 3, 23, 4, 6, 7, 14, 8, 10, 11, 12, 13, 20, 15, 16, 17, 18, 5, 9, 21, 22, 19]
  left_inv := by decide
  right_inv := by decide

def diagGen7 : Equiv.Perm (Fin 24) where
  toFun := ![0, 12, 4, 3, 15, 5, 6, 7, 8, 1, 9, 11, 10, 13, 14, 17, 16, 2, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 9, 17, 3, 2, 5, 6, 7, 8, 10, 12, 11, 1, 13, 14, 4, 16, 15, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def diagGen : Fin 8 → Equiv.Perm (Fin 24) := ![diagGen0, diagGen1, diagGen2, diagGen3, diagGen4, diagGen5, diagGen6, diagGen7]

def quarterGen0 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 12, 13, 14, 11, 10, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 16, 15, 12, 13, 14, 10, 11, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def quarterGen1 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 5, 19, 6, 7, 9, 20, 10, 11, 12, 13, 8, 15, 16, 17, 18, 23, 14, 21, 22, 4]
  invFun := ![0, 1, 2, 3, 23, 4, 6, 7, 14, 8, 10, 11, 12, 13, 20, 15, 16, 17, 18, 5, 9, 21, 22, 19]
  left_inv := by decide
  right_inv := by decide

def quarterGen2 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 18, 17, 8, 9, 10, 11, 6, 7, 14, 15, 16, 21, 22, 19, 20, 13, 12, 23]
  invFun := ![0, 1, 2, 3, 4, 5, 12, 13, 8, 9, 10, 11, 22, 21, 14, 15, 16, 7, 6, 19, 20, 17, 18, 23]
  left_inv := by decide
  right_inv := by decide

def quarterGen3 : Equiv.Perm (Fin 24) where
  toFun := ![2, 3, 1, 0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![3, 2, 0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def quarterGen4 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 17, 10, 11, 12, 13, 14, 15, 16, 18, 19, 9, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 19, 10, 11, 12, 13, 14, 15, 16, 9, 17, 18, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def quarterGen5 : Equiv.Perm (Fin 24) where
  toFun := ![0, 21, 2, 20, 4, 1, 3, 7, 8, 9, 10, 5, 12, 13, 14, 6, 16, 17, 18, 19, 15, 11, 22, 23]
  invFun := ![0, 5, 2, 6, 4, 11, 15, 7, 8, 9, 10, 21, 12, 13, 14, 20, 16, 17, 18, 19, 3, 1, 22, 23]
  left_inv := by decide
  right_inv := by decide

def quarterGen6 : Equiv.Perm (Fin 24) where
  toFun := ![23, 1, 22, 3, 4, 5, 6, 0, 2, 9, 7, 11, 12, 13, 14, 15, 8, 17, 18, 19, 20, 21, 16, 10]
  invFun := ![7, 1, 8, 3, 4, 5, 6, 10, 16, 9, 23, 11, 12, 13, 14, 15, 22, 17, 18, 19, 20, 21, 2, 0]
  left_inv := by decide
  right_inv := by decide

def quarterGen7 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 12, 5, 6, 7, 8, 9, 10, 11, 13, 14, 4, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 14, 5, 6, 7, 8, 9, 10, 11, 4, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def quarterGen8 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 20]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 23, 20, 21, 22]
  left_inv := by decide
  right_inv := by decide

def quarterGen9 : Equiv.Perm (Fin 24) where
  toFun := ![14, 1, 2, 13, 4, 5, 6, 7, 8, 9, 10, 18, 12, 16, 11, 15, 19, 17, 0, 3, 20, 21, 22, 23]
  invFun := ![18, 1, 2, 19, 4, 5, 6, 7, 8, 9, 10, 14, 12, 3, 0, 15, 13, 17, 11, 16, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def quarterGen10 : Equiv.Perm (Fin 24) where
  toFun := ![0, 12, 4, 3, 15, 5, 6, 7, 8, 1, 9, 11, 10, 13, 14, 17, 16, 2, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 9, 17, 3, 2, 5, 6, 7, 8, 10, 12, 11, 1, 13, 14, 4, 16, 15, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def quarterGen11 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 6, 7, 8, 5, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 4, 8, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def quarterGen : Fin 12 → Equiv.Perm (Fin 24) := ![quarterGen0, quarterGen1, quarterGen2, quarterGen3, quarterGen4, quarterGen5, quarterGen6, quarterGen7, quarterGen8, quarterGen9, quarterGen10, quarterGen11]

def diagonalThreeCycle : Equiv.Perm (Fin 24) :=
  let P := (diagGen 6)⁻¹ * diagGen 5 * diagGen 6
  let Q := diagGen 7
  P * Q * P⁻¹ * Q⁻¹

end RubikExceptional
