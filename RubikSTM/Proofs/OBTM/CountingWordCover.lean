import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn
set_option autoImplicit false

theorem proof_RubikOBTM_CountingWordCover {State Move : Type*} [Fintype State] [Fintype Move]
    (step : State → Move → State) (start : State) (d : ℕ)
    (cover : ∀ s : State, ∃ w : List Move,
      w.length ≤ d ∧ w.foldl step start = s) :
    Fintype.card State ≤
      ∑ j ∈ Finset.range (d + 1), Fintype.card Move ^ j := by
  classical
  let Words := Σ j : Fin (d + 1), (Fin j.val → Move)
  let eval : Words → State := fun w => (List.ofFn w.2).foldl step start
  have heval : Function.Surjective eval := by
    intro s
    obtain ⟨w, hw, hs⟩ := cover s
    refine ⟨⟨⟨w.length, Nat.lt_succ_of_le hw⟩, w.get⟩, ?_⟩
    simpa [eval] using hs
  calc
    Fintype.card State ≤ Fintype.card Words :=
      Fintype.card_le_of_surjective eval heval
    _ = ∑ j : Fin (d + 1), Fintype.card Move ^ (j : ℕ) := by
      simp [Words, Fintype.card_sigma]
    _ = ∑ j ∈ Finset.range (d + 1), Fintype.card Move ^ j :=
      Fin.sum_univ_eq_sum_range _ (d + 1)

#print axioms proof_RubikOBTM_CountingWordCover
