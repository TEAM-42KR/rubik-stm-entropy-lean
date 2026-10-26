import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Lemmas.OBTM.BlockWordDistance
set_option autoImplicit false

theorem proof_RubikOBTM_diameter_le_uniform_word_bound {n : ℕ} (B : ℝ)
    (h : ∀ u v : Rubik.Position n, ∃ w : List (RubikOBTM.BlockMove n),
      (w.length : ℝ) ≤ B ∧ RubikOBTM.applyBlockWord w u.val = v.val) :
    (RubikOBTM.obtmDiameter n : ℝ) ≤ B := by
  letI : Nonempty (Rubik.Position n) := ⟨⟨Rubik.solved n, ⟨[], rfl⟩⟩⟩
  obtain ⟨u, v, hd⟩ := (RubikOBTM.obtmGraph n).exists_dist_eq_diam
  obtain ⟨w, hw, he⟩ := h u v
  change ((RubikOBTM.obtmGraph n).diam : ℝ) ≤ B
  rw [← hd]
  have hdist : ((RubikOBTM.obtmGraph n).dist u v : ℝ) ≤ (w.length : ℝ) := by
    exact_mod_cast RubikOBTM.blockWord_distance w u v he
  exact hdist.trans hw
