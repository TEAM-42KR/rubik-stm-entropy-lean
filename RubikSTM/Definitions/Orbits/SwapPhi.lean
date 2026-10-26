import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Definitions.Bands.Band
import RubikSTM.Definitions.Intertwiners.SurfaceFlip
set_option autoImplicit false

namespace RubikOrbit

def swapPhi : Equiv.Perm (Fin 24) where
  toFun := ![3, 2, 0, 1, 14, 8, 5, 6, 7, 17, 15, 16, 4, 12, 13, 11, 10, 18, 19, 9, 21, 22, 23, 20]
  invFun := ![2, 3, 1, 0, 12, 6, 7, 8, 5, 19, 16, 15, 13, 14, 4, 10, 11, 9, 17, 18, 23, 20, 21, 22]
  left_inv := by decide
  right_inv := by decide

def minusLab {n : ℕ} (a b : Fin n) (hb : 0 < b.val ∧ b.val + 1 < n)
    (i : Fin 24) : Rubik.Sticker n :=
  RubikIntertwiner.surfaceFlip b hb (RubikGeometry.lab a b i)

def minusB : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 13, 4, 5, 6, 7, 8, 9, 10, 11, 12, 16, 14, 15, 19, 17, 18, 3, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 19, 4, 5, 6, 7, 8, 9, 10, 11, 12, 3, 14, 15, 13, 17, 18, 16, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide
end RubikOrbit
