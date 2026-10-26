import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
import RubikSTM.Definitions.Core.CoreAction
set_option autoImplicit false

theorem proof_RubikGlobalWord_task_same_iff {n h : ℕ} (f : RubikGlobal.I n → Fin h) (p : RubikGlobal.Q n)
  (r : RubikGlobalWord.SamePair f) :
  RubikGlobalWord.taskOf f p = Sum.inr r ↔ p = r.val := by
  by_cases he : p = r.val
  · subst p
    simp [RubikGlobalWord.taskOf, r.property]
  · unfold RubikGlobalWord.taskOf
    split_ifs <;> simp_all [Subtype.ext_iff]

#print axioms proof_RubikGlobalWord_task_same_iff
