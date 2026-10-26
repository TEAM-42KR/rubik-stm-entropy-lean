import RubikSTM.Proofs.Asymptotics.LowerTail
import RubikSTM.Definitions.Geometry.StmGraph
set_option autoImplicit false

theorem RubikAsymptotics.lowerTail :
    ∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ n : ℕ in Filter.atTop, Rubik.entropyConstant - ε ≤ Rubik.normalizedDiameter n :=
  @proof_RubikAsymptotics_lowerTail
