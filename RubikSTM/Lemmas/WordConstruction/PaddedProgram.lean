import RubikSTM.Proofs.WordConstruction.PaddedProgram
import Mathlib
set_option autoImplicit false

theorem RubikCompiler.paddedProgram :
    ∀ {G X : Type*} [Group G] [MulAction G X]
  (B : G) (hB : B ^ 4 = 1) (t j : ℕ)
  (hj : 1 ≤ j) (hjt : j ≤ t) (ht : t % 4 = 1)
  (Fs : List G) (x y : X)
  (hraw : Fs.reverse.prod • (B ^ ((j-1) % 4) • x) =
    B ^ ((j-1) % 4) • y), (Fs.map (fun F => B ^ (t-j) * F * B ^ (j-1))).reverse.prod =
      (B ^ ((j-1) % 4))⁻¹ * Fs.reverse.prod * B ^ ((j-1) % 4) ∧
    (Fs.map (fun F => B ^ (t-j) * F * B ^ (j-1))).reverse.prod • x = y :=
  @proof_RubikCompiler_paddedProgram
