import RubikSTM.Definitions.Solved.Metrics
set_option autoImplicit false

theorem proof_RubikSolved_solvedLooking_card_le (n : ℕ) :
    Nat.card {p : Rubik.Position n // RubikSolved.IsSolvedLooking p} ≤ 6 ^ 6 := by
  classical
  let f : {p : Rubik.Position n // RubikSolved.IsSolvedLooking p} →
      (Rubik.Normal → Rubik.Colour) := fun p => Classical.choose p.property
  have hf : Function.Injective f := by
    intro p q hpq
    apply Subtype.ext
    apply Subtype.ext
    funext s
    calc
      p.val.val s = f p s.val.2 := Classical.choose_spec p.property s
      _ = f q s.val.2 := congrFun hpq s.val.2
      _ = q.val.val s := (Classical.choose_spec q.property s).symm
  have h := Fintype.card_le_of_injective f hf
  simpa [Nat.card_eq_fintype_card, Rubik.Normal, Rubik.Colour, Rubik.Axis] using h
