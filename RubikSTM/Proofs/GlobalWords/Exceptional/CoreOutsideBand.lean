import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
import RubikSTM.Definitions.Core.CoreAction
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open Rubik RubikGlobal RubikGlobalWord
theorem proof_RubikGlobalWord_Exceptional_core_outside_band {n : ℕ} (i : I n) (s : Sticker n)
    (hs : RubikCore.IsCore s) : ¬ RubikBand.Band (depth i) s := by
  have hi := i.isLt
  have hlevel : ¬ RubikCore.IsLevel (depth i) := by
    intro h
    rcases h with h | h | h
    · simp only [depth, Fin.val_mk] at h
      omega
    · simp only [depth, Fin.val_mk] at h
      omega
    · have hv := congrArg Fin.val h
      simp only [Fin.val_rev, depth, Fin.val_mk] at hv
      omega
  have hrev : ¬ RubikCore.IsLevel (depth i).rev := by
    intro h
    exact hlevel ((RubikCore.Internal.isLevel_rev _).mp h)
  rintro ⟨ax, h | h⟩
  · exact hlevel (h ▸ hs ax)
  · exact hrev (h ▸ hs ax)
