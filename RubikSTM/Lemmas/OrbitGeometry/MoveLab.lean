import RubikSTM.Proofs.OrbitGeometry.MoveLab
import RubikSTM.Definitions.OrbitGeometry.GenPerm
set_option autoImplicit false
open Rubik RubikGeometry

theorem RubikGeometry.move_lab :
    ∀ {n : ℕ} {a b : Fin n} (hg : RubikGeometry.Generic n a b) (k : Fin 8) (i : Fin 24), Rubik.movePermutation (RubikGeometry.genMove a b k) (RubikGeometry.lab a b i) = RubikGeometry.lab a b (RubikGeometry.genPerm k i) :=
  @proof_RubikGeometry_move_lab
