import RubikSTM.Proofs.Orbits.PairedQuarter
import RubikSTM.Definitions.Orbits.SwapPhi
set_option autoImplicit false

theorem RubikOrbit.pairedQuarter :
    ∀ {n : ℕ} {a b : Fin n} (hg : RubikGeometry.Generic n a b)
  (hb : 0 < b.val ∧ b.val + 1 < n) (i : Fin 24), Rubik.sliceQuarter n 2 b.rev (RubikGeometry.lab a b i) =
      RubikGeometry.lab a b (RubikGeometry.gen7 i) ∧
    Rubik.sliceQuarter n 2 b.rev (RubikOrbit.minusLab a b hb i) =
      RubikOrbit.minusLab a b hb (RubikOrbit.minusB i) :=
  @proof_RubikOrbit_pairedQuarter
