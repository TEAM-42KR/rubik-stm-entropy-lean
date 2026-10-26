import RubikSTM.Proofs.Orbits.BandIntersection
import RubikSTM.Definitions.Orbits.SwapPhi
set_option autoImplicit false

theorem RubikOrbit.bandIntersection :
    ∀ {n : ℕ} {a b : Fin n} (hg : RubikGeometry.Generic n a b) (s : Rubik.Sticker n), (RubikBand.Band a s ∧ RubikBand.Band b s) ↔
    s ∈ Set.range (RubikGeometry.lab a b) ∪ Set.range (RubikGeometry.lab b a) :=
  @proof_RubikOrbit_bandIntersection
