import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn
set_option autoImplicit false

theorem proof_RubikSolved_multiSourceWordCount {State Source Move : Type*}
    [Fintype State] [Fintype Source] [Fintype Move]
    (run : Source → List Move → State) (d : ℕ)
    (cover : ∀ p : State, ∃ q : Source, ∃ w : List Move,
      w.length ≤ d ∧ run q w = p) :
    Fintype.card State ≤ Fintype.card Source *
      ∑ j ∈ Finset.range (d + 1), Fintype.card Move ^ j := by
  classical
  let Words := Σ j : Fin (d + 1), (Fin j.val → Move)
  let eval : Source × Words → State := fun c => run c.1 (List.ofFn c.2.2)
  have heval : Function.Surjective eval := by
    intro p
    obtain ⟨q, w, hw, hs⟩ := cover p
    refine ⟨(q, ⟨⟨w.length, Nat.lt_succ_of_le hw⟩, w.get⟩), ?_⟩
    simpa [eval] using hs
  calc
    Fintype.card State ≤ Fintype.card (Source × Words) :=
      Fintype.card_le_of_surjective eval heval
    _ = Fintype.card Source *
        ∑ j : Fin (d + 1), Fintype.card Move ^ (j : ℕ) := by
      simp [Words, Fintype.card_sigma]
    _ = Fintype.card Source *
        ∑ j ∈ Finset.range (d + 1), Fintype.card Move ^ j := by
      rw [Fin.sum_univ_eq_sum_range]
