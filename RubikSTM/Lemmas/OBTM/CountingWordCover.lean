import RubikSTM.Proofs.OBTM.CountingWordCover
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn
set_option autoImplicit false

theorem RubikOBTM.CountingWordCover :
    ∀ {State Move : Type*} [Fintype State] [Fintype Move] (step : State → Move → State) (start : State) (d : ℕ) (cover : ∀ s : State, ∃ w : List Move, w.length ≤ d ∧ w.foldl step start = s), Fintype.card State ≤ ∑ j ∈ Finset.range (d + 1), Fintype.card Move ^ j :=
  @proof_RubikOBTM_CountingWordCover
