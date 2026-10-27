import RubikSTM.Definitions.Geometry.StmGraph
set_option autoImplicit false

theorem proof_Rubik_stmGraph_connected (n : ℕ) : (Rubik.stmGraph n).Connected := by
  classical
  let p (w : List (Rubik.Move n)) : Rubik.Position n :=
    ⟨Rubik.applyWord w (Rubik.solved n), ⟨w, rfl⟩⟩
  have hstep (w : List (Rubik.Move n)) (m : Rubik.Move n) :
      (Rubik.stmGraph n).Reachable (p w) (p (w ++ [m])) := by
    by_cases h : p w = p (w ++ [m])
    · exact h ▸ SimpleGraph.Reachable.refl (p w)
    · apply SimpleGraph.Adj.reachable
      refine ⟨h, Or.inl ⟨m, ?_⟩⟩
      simp [p, Rubik.applyWord, List.foldl_append]
  have hall : ∀ w : List (Rubik.Move n), (Rubik.stmGraph n).Reachable (p []) (p w) := by
    intro w
    induction w using List.reverseRecOn with
    | nil => exact SimpleGraph.Reachable.refl _
    | append_singleton w m ih => exact ih.trans (hstep w m)
  apply (SimpleGraph.connected_iff_exists_forall_reachable (Rubik.stmGraph n)).mpr
  refine ⟨p [], ?_⟩
  intro c
  obtain ⟨w, hw⟩ := c.property
  have hc : p w = c := Subtype.ext hw
  simpa only [hc] using hall w

#print axioms proof_Rubik_stmGraph_connected
