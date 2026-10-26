import RubikSTM.Proofs.GlobalWords.GroupsAdmissible
import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
set_option autoImplicit false

theorem RubikGlobalWord.groups_admissible :
    ∀ {n h : ℕ} (f : RubikGlobal.I n → Fin h) (r : RubikGlobalWord.GroupPair h), RubikPayload.Admissible (RubikGlobalWord.depthGroup f r.val.1)
    (RubikGlobalWord.depthGroup f r.val.2) :=
  @proof_RubikGlobalWord_groups_admissible
