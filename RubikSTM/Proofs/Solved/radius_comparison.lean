import RubikSTM.Definitions.Solved.Metrics
import RubikSTM.Lemmas.Solved.solved_looks_solved
import RubikSTM.Lemmas.Solved.solvedLookingDistance_le
set_option autoImplicit false

theorem proof_RubikSolved_radius_comparison {n : ℕ} (G : SimpleGraph (Rubik.Position n)) (hc : G.Connected) :
    RubikSolved.solvedLookingRadius G ≤ RubikSolved.solvedRadius G ∧
      RubikSolved.solvedRadius G ≤ G.diam := by
  classical
  constructor
  · apply Finset.sup_le
    intro p _
    exact (RubikSolved.solvedLookingDistance_le G p (RubikSolved.solvedPosition n)
      (RubikSolved.solved_looks_solved n)).trans
        (Finset.le_sup (f := fun x : Rubik.Position n =>
          G.dist x (RubikSolved.solvedPosition n)) (Finset.mem_univ p))
  · apply Finset.sup_le
    intro p _
    letI : Nonempty (Rubik.Position n) := ⟨RubikSolved.solvedPosition n⟩
    exact G.dist_le_diam (G.connected_iff_ediam_ne_top.mp hc)
