import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
import RubikSTM.Definitions.Core.CoreAction
import RubikSTM.Lemmas.GlobalWords.TaskSameIff
set_option autoImplicit false

theorem proof_RubikGlobalWord_region_same {n h : ℕ} (f : RubikGlobal.I n → Fin h) (p : RubikGlobalWord.SamePair f) :
  RubikGlobalWord.Region f (Sum.inr p) = RubikGlobal.GenericRange p.val := by
  ext s
  simp only [RubikGlobalWord.Region, Set.mem_setOf_eq, RubikGlobalWord.task_same_iff]
  exact ⟨by rintro ⟨p,rfl,hs⟩; exact hs, fun hs => ⟨p.val,rfl,hs⟩⟩

#print axioms proof_RubikGlobalWord_region_same
