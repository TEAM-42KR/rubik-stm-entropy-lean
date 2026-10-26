import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
import RubikSTM.Definitions.Core.CoreAction
set_option autoImplicit false

theorem proof_RubikGlobalWord_task_pair_iff {n h : ℕ} (f : RubikGlobal.I n → Fin h) (p : RubikGlobal.Q n)
  (r : RubikGlobalWord.GroupPair h) :
  RubikGlobalWord.taskOf f p = Sum.inl r ↔
    (f p.val.1 = r.val.1 ∧ f p.val.2 = r.val.2) ∨
    (f p.val.2 = r.val.1 ∧ f p.val.1 = r.val.2) := by
  rcases r with ⟨⟨u,v⟩,huv⟩
  dsimp only at huv ⊢
  unfold RubikGlobalWord.taskOf
  split_ifs with hp hq <;>
    try simp only [Sum.inl.injEq, Sum.inr_ne_inl, Subtype.ext_iff, Prod.mk.injEq]
  all_goals
    constructor
    · intro H
      first | exact Or.inl H | exact Or.inr H | exact H.elim
    · rintro (⟨h₁,h₂⟩ | ⟨h₁,h₂⟩) <;> first | exact ⟨h₁,h₂⟩ | omega

#print axioms proof_RubikGlobalWord_task_pair_iff
