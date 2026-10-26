import RubikSTM.Proofs.GlobalWords.TaskSameIff
import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
set_option autoImplicit false

theorem RubikGlobalWord.task_same_iff :
    ∀ {n h : ℕ} (f : RubikGlobal.I n → Fin h) (p : RubikGlobal.Q n)
  (r : RubikGlobalWord.SamePair f), RubikGlobalWord.taskOf f p = Sum.inr r ↔ p = r.val :=
  @proof_RubikGlobalWord_task_same_iff
