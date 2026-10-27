import RubikSTM.Definitions.Geometry.StmGraph
set_option autoImplicit false

namespace RubikSolved

def solvedPosition (n : ℕ) : Rubik.Position n :=
  ⟨Rubik.solved n, ⟨[], rfl⟩⟩

def IsSolvedLooking {n : ℕ} (p : Rubik.Position n) : Prop :=
  ∃ faceColour : Rubik.Normal → Rubik.Colour,
    ∀ s : Rubik.Sticker n, p.val s = faceColour s.val.2

noncomputable def solvedRadius {n : ℕ} (G : SimpleGraph (Rubik.Position n)) : ℕ :=
  Finset.univ.sup (fun p => G.dist p (solvedPosition n))

noncomputable def solvedLookingDistance {n : ℕ}
    (G : SimpleGraph (Rubik.Position n)) (p : Rubik.Position n) : ℕ :=
  sInf {d : ℕ | ∃ q : Rubik.Position n, IsSolvedLooking q ∧ G.dist p q = d}

noncomputable def solvedLookingRadius {n : ℕ}
    (G : SimpleGraph (Rubik.Position n)) : ℕ :=
  Finset.univ.sup (solvedLookingDistance G)

noncomputable def metrics {n : ℕ} (G : SimpleGraph (Rubik.Position n)) : ℕ × ℕ :=
  (solvedRadius G, solvedLookingRadius G)

end RubikSolved
