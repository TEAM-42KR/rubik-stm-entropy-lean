import RubikSTM.Proofs.Core.FiniteWordCompression
import Mathlib
set_option autoImplicit false

theorem RubikCore.finite_word_compression :
    ∀ {M X : Type*} [Fintype X] (step : X → M → X) (x y : X) (h : ∃ w : List M, w.foldl step x = y), ∃ w : List M, w.length < Fintype.card X ∧ w.foldl step x = y :=
  @proof_RubikCore_finite_word_compression
