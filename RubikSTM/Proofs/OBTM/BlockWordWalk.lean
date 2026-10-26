import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Lemmas.OBTM.BlockReachable
set_option autoImplicit false

theorem proof_RubikOBTM_blockWord_walk {n : ℕ} (w : List (RubikOBTM.BlockMove n)) (u v : Rubik.Position n)
    (h : RubikOBTM.applyBlockWord w u.val = v.val) :
    ∃ p : (RubikOBTM.obtmGraph n).Walk u v, p.length ≤ w.length := by
  classical
  induction w generalizing u with
  | nil =>
    have he : u = v := Subtype.ext h
    subst v
    exact ⟨.nil, by simp⟩
  | cons m w ih =>
    let mid : Rubik.Position n :=
      ⟨RubikOBTM.applyBlock m u.val, RubikOBTM.block_reachable m u.val u.property⟩
    have htail : RubikOBTM.applyBlockWord w mid.val = v.val := h
    obtain ⟨p, hp⟩ := ih mid htail
    by_cases he : u = mid
    · refine ⟨p.copy he.symm rfl, ?_⟩
      simp only [SimpleGraph.Walk.length_copy, List.length_cons]
      omega
    · have hedge : (RubikOBTM.obtmGraph n).Adj u mid := ⟨he, Or.inl ⟨m, rfl⟩⟩
      refine ⟨SimpleGraph.Walk.cons hedge p, ?_⟩
      change p.length + 1 ≤ w.length + 1
      omega
