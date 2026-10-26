import RubikSTM.Proofs.Orbits.FlipLabel
import RubikSTM.Definitions.Orbits.SwapPhi
set_option autoImplicit false

theorem RubikOrbit.flipLabel :
    ∀ {n : ℕ} {a b : Fin n} (hg : RubikGeometry.Generic n a b)
  (hb : 0 < b.val ∧ b.val + 1 < n) (i : Fin 24), RubikOrbit.minusLab a b hb i = RubikGeometry.lab b a (RubikOrbit.swapPhi i) :=
  @proof_RubikOrbit_flipLabel
