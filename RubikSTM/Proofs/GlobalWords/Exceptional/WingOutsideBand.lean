import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
import RubikSTM.Definitions.Core.CoreAction
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open Rubik RubikGlobal RubikGlobalWord
theorem proof_RubikGlobalWord_Exceptional_wing_outside_band {n : ℕ} (i j : I n) (hij : i ≠ j)
    (s : Sticker n) (hs : s ∈ WingRange j) : ¬ RubikBand.Band (depth i) s := by
  have hi := i.isLt
  have hj := j.isLt
  have hijv : i.val ≠ j.val := fun h => hij (Fin.ext h)
  obtain ⟨l, side, rfl⟩ := hs
  rintro ⟨ax, hax⟩
  fin_cases l <;> fin_cases ax <;>
    simp [RubikWing.lab, RubikWing.pos, coordinate, RubikWing.lo, RubikWing.hi,
      depth, Fin.ext_iff, Fin.rev] at hax <;> omega
