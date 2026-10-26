import RubikSTM.Proofs.WordConstruction.PowModFour
import Mathlib
set_option autoImplicit false

theorem RubikCompiler.powModFour :
    ∀ {G : Type*} [Group G] (B : G) (hB : B ^ 4 = 1) (m : ℕ), B ^ m = B ^ (m % 4) :=
  @proof_RubikCompiler_powModFour
