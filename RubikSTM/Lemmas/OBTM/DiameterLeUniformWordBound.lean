import RubikSTM.Proofs.OBTM.DiameterLeUniformWordBound
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikOBTM.diameter_le_uniform_word_bound :
    ∀ {n : ℕ} (B : ℝ) (h : ∀ u v : Rubik.Position n, ∃ w : List (RubikOBTM.BlockMove n), (w.length : ℝ) ≤ B ∧ RubikOBTM.applyBlockWord w u.val = v.val), (RubikOBTM.obtmDiameter n : ℝ) ≤ B :=
  @proof_RubikOBTM_diameter_le_uniform_word_bound
