import RubikSTM.Definitions.Solved.Metrics
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

namespace Rubik

noncomputable def solvedRadius (n : ℕ) : ℕ :=
  RubikSolved.solvedRadius (stmGraph n)

noncomputable def solvedLookingRadius (n : ℕ) : ℕ :=
  RubikSolved.solvedLookingRadius (stmGraph n)

noncomputable def normalizedSolvedRadius (n : ℕ) : ℝ :=
  (solvedRadius n : ℝ) * Real.log (n : ℝ) / (n : ℝ)^2

noncomputable def normalizedSolvedLookingRadius (n : ℕ) : ℝ :=
  (solvedLookingRadius n : ℝ) * Real.log (n : ℝ) / (n : ℝ)^2

end Rubik

namespace RubikOBTM

noncomputable def solvedRadius (n : ℕ) : ℕ :=
  RubikSolved.solvedRadius (obtmGraph n)

noncomputable def solvedLookingRadius (n : ℕ) : ℕ :=
  RubikSolved.solvedLookingRadius (obtmGraph n)

noncomputable def normalizedSolvedRadius (n : ℕ) : ℝ :=
  (solvedRadius n : ℝ) * Real.log (n : ℝ) / (n : ℝ)^2

noncomputable def normalizedSolvedLookingRadius (n : ℕ) : ℝ :=
  (solvedLookingRadius n : ℝ) * Real.log (n : ℝ) / (n : ℝ)^2

end RubikOBTM
