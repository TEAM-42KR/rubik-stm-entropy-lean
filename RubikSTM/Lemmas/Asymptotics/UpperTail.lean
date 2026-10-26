import RubikSTM.Proofs.Asymptotics.UpperTail
import RubikSTM.Definitions.Geometry.StmGraph
set_option autoImplicit false

theorem RubikAsymptotics.upperTail :
    ∀ (ε : ℝ) (hε : 0 < ε), ∀ᶠ n : ℕ in Filter.atTop, Rubik.normalizedDiameter n ≤ Rubik.entropyConstant + ε :=
  @proof_RubikAsymptotics_upperTail
