import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
set_option autoImplicit false

theorem proof_RubikGlobalWord_sum_group_pairs {h : ℕ} {M : Type*} [AddCommMonoid M] (F : Fin h → Fin h → M) :
  (∑ p : RubikGlobalWord.GroupPair h, F p.val.1 p.val.2) =
    ∑ i : Fin h, ∑ j : Fin h, if i < j then F i j else 0 := by
  simpa only [Finset.subtype_univ,Finset.sum_filter,Fintype.sum_prod_type] using
    (Finset.sum_subtype_eq_sum_filter (s:=(Finset.univ : Finset (Fin h × Fin h)))
      (p:=fun p => p.1<p.2) (fun p => F p.1 p.2))

#print axioms proof_RubikGlobalWord_sum_group_pairs
