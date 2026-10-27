import RubikSTM.Proofs.Solved.multiSourceWordCount
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn
set_option autoImplicit false

theorem RubikSolved.multiSourceWordCount :
    ∀ {State Source Move : Type*} [Fintype State] [Fintype Source] [Fintype Move] (run : Source → List Move → State) (d : ℕ) (cover : ∀ p : State, ∃ q : Source, ∃ w : List Move, w.length ≤ d ∧ run q w = p), Fintype.card State ≤ Fintype.card Source * ∑ j ∈ Finset.range (d + 1), Fintype.card Move ^ j :=
  @proof_RubikSolved_multiSourceWordCount
