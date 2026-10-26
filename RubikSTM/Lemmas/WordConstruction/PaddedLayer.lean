import RubikSTM.Proofs.WordConstruction.PaddedLayer
import Mathlib
set_option autoImplicit false

theorem RubikCompiler.paddedLayer :
    ∀ {G : Type*} [Group G] (B F : G) (hB : B ^ 4 = 1)
  (t j : ℕ) (hj : 1 ≤ j) (hjt : j ≤ t) (ht : t % 4 = 1), B ^ (t-j) * F * B ^ (j-1) =
    (B ^ ((j-1) % 4))⁻¹ * F * B ^ ((j-1) % 4) :=
  @proof_RubikCompiler_paddedLayer
