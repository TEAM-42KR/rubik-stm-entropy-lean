import RubikSTM.Proofs.OBTM.GlobalWords.SumGroupPairs
import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
set_option autoImplicit false

theorem RubikGlobalWord.sum_group_pairs :
    ∀ {h : ℕ} {M : Type*} [AddCommMonoid M] (F : Fin h → Fin h → M), (∑ p : RubikGlobalWord.GroupPair h, F p.val.1 p.val.2) =
    ∑ i : Fin h, ∑ j : Fin h, if i < j then F i j else 0 :=
  @proof_RubikGlobalWord_sum_group_pairs
