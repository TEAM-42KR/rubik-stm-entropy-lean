import RubikSTM.Proofs.Orbits.PlusQuarter
import RubikSTM.Definitions.Orbits.SwapPhi
set_option autoImplicit false

theorem RubikOrbit.plusQuarter :
    ∀ {n : ℕ} {a b : Fin n} (hg : RubikGeometry.Generic n a b) (i : Fin 24), Rubik.sliceQuarter n 2 b.rev (RubikGeometry.lab a b i) =
    RubikGeometry.lab a b (RubikGeometry.gen7 i) :=
  @proof_RubikOrbit_plusQuarter
