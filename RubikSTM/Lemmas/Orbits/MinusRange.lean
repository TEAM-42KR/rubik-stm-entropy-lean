import RubikSTM.Proofs.Orbits.MinusRange
import RubikSTM.Definitions.Orbits.SwapPhi
set_option autoImplicit false

theorem RubikOrbit.minusRange :
    ∀ {n : ℕ} {a b : Fin n} (hg : RubikGeometry.Generic n a b)
  (hb : 0 < b.val ∧ b.val + 1 < n), Set.range (RubikOrbit.minusLab a b hb) = Set.range (RubikGeometry.lab b a) :=
  @proof_RubikOrbit_minusRange
