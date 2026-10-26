import RubikSTM.Definitions.OrbitGeometry.GenPerm
set_option autoImplicit false
namespace RubikOrbit
def rigid0 : Equiv.Perm (Fin 24) where
  toFun := ![2, 3, 1, 0, 5, 19, 18, 17, 9, 20, 15, 16, 6, 7, 8, 11, 10, 21, 22, 23, 14, 13, 12, 4]
  invFun := ![3, 2, 0, 1, 23, 4, 12, 13, 14, 8, 16, 15, 22, 21, 20, 10, 11, 7, 6, 5, 9, 17, 18, 19]
  left_inv := by decide
  right_inv := by decide

def rigid1 : Equiv.Perm (Fin 24) where
  toFun := ![23, 21, 22, 20, 12, 1, 3, 0, 2, 17, 7, 5, 13, 14, 4, 6, 8, 18, 19, 9, 15, 11, 16, 10]
  invFun := ![7, 5, 8, 6, 14, 11, 15, 10, 16, 19, 23, 21, 4, 12, 13, 20, 22, 9, 17, 18, 3, 1, 2, 0]
  left_inv := by decide
  right_inv := by decide

def rigid2 : Equiv.Perm (Fin 24) where
  toFun := ![14, 12, 4, 13, 15, 6, 7, 8, 5, 1, 9, 18, 10, 16, 11, 17, 19, 2, 0, 3, 21, 22, 23, 20]
  invFun := ![18, 9, 17, 19, 2, 8, 5, 6, 7, 10, 12, 14, 1, 3, 0, 4, 13, 15, 11, 16, 23, 20, 21, 22]
  left_inv := by decide
  right_inv := by decide

def rigidLabelPermutation : Rubik.Axis → Equiv.Perm (Fin 24) := ![rigid0, rigid1, rigid2]
end RubikOrbit
