import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
import RubikSTM.Definitions.Core.CoreAction
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open Rubik RubikGlobal RubikGlobalWord
theorem proof_RubikGlobalWord_Exceptional_midpoint_unique {n : ℕ} (m k : Fin n) (hm : m.rev = m) (hk : k.rev = k) : m = k := by
  apply Fin.ext
  have hm' := congrArg Fin.val hm
  have hk' := congrArg Fin.val hk
  simp only [Fin.val_rev] at hm' hk'
  omega
