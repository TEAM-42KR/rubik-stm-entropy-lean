import RubikSTM.Proofs.Core.FinitePermutationWordRollback
import Mathlib
set_option autoImplicit false

theorem RubikCore.finite_permutation_word_rollback :
    ∀ {M X : Type*} [Fintype X] (p : M → Equiv.Perm X) (w : List M) (x : X), ∃ v : List M, v.foldl (fun z m => p m z) (w.foldl (fun z m => p m z) x) = x :=
  @proof_RubikCore_finite_permutation_word_rollback
