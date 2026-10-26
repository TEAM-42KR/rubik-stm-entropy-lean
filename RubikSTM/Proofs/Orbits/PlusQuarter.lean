import RubikSTM.Definitions.Orbits.SwapPhi
import RubikSTM.Lemmas.OrbitGeometry.MoveLab
set_option autoImplicit false

theorem proof_RubikOrbit_plusQuarter {n : ℕ} {a b : Fin n} (hg : RubikGeometry.Generic n a b) (i : Fin 24) :
  Rubik.sliceQuarter n 2 b.rev (RubikGeometry.lab a b i) =
    RubikGeometry.lab a b (RubikGeometry.gen7 i) := by
  simpa [RubikGeometry.genMove, RubikGeometry.genPerm, Rubik.movePermutation] using
    (RubikGeometry.move_lab hg (7 : Fin 8) i)

#print axioms proof_RubikOrbit_plusQuarter
