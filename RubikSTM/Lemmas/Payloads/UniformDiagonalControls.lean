import RubikSTM.Proofs.Payloads.UniformDiagonalControls
import Mathlib
import RubikSTM.Definitions.Payloads.Realizes
set_option autoImplicit false

theorem RubikPayload.uniformDiagonalControls :
    ∃ K : ℕ, ∀ (n : ℕ) (a : Fin n), RubikPayload.Half a →
  ∀ σ : Equiv.Perm (Fin 24), ∃ w : List (Rubik.Move n),
    w.length ≤ K ∧ RubikBand.StrictControl a w ∧
    ∀ (b : Fin n), RubikGeometry.Generic n a b →
      (∀ i, RubikBand.wordPerm w (RubikGeometry.lab a b i) = RubikGeometry.lab a b (σ i)) ∧
      (∀ hb : 0 < b.val ∧ b.val + 1 < n, ∀ i,
        RubikBand.wordPerm w (RubikOrbit.minusLab a b hb i) =
          RubikOrbit.minusLab a b hb (σ i)) :=
  @proof_RubikPayload_uniformDiagonalControls
