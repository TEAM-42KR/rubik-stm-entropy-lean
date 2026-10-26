import RubikSTM.Proofs.GlobalWords.TaskPairIff
import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
set_option autoImplicit false

theorem RubikGlobalWord.task_pair_iff :
    ∀ {n h : ℕ} (f : RubikGlobal.I n → Fin h) (p : RubikGlobal.Q n)
  (r : RubikGlobalWord.GroupPair h), RubikGlobalWord.taskOf f p = Sum.inl r ↔
    (f p.val.1 = r.val.1 ∧ f p.val.2 = r.val.2) ∨
    (f p.val.2 = r.val.1 ∧ f p.val.1 = r.val.2) :=
  @proof_RubikGlobalWord_task_pair_iff
