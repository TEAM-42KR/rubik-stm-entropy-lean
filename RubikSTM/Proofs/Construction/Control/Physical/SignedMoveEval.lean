import Mathlib
import RubikSTM.Definitions.Construction.Control.Physical.ActualMoves
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Lemmas.Construction.Control.Physical.QuarterInverse
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open Rubik RubikConstruction.Control RubikConstruction.Control.Physical
theorem proof_RubikConstruction_Control_Physical_signed_move_eval {n : ℕ} (a : Fin n) (t : SignedLetter) :
    movePermutation (signedMove a t) =
      if t.2 then physicalAtom a t.1 else (physicalAtom a t.1)⁻¹ := by
  rcases t with ⟨t, s⟩
  have hp : ((positiveMove a t).1, (positiveMove a t).2.1, (0 : Fin 3)) = positiveMove a t := by
    cases t with
    | inl f => fin_cases f <;> rfl
    | inr ax => rfl
  have he : movePermutation (positiveMove a t) = physicalAtom a t := by
    cases t <;> rfl
  cases s
  · change movePermutation ((positiveMove a t).1, (positiveMove a t).2.1, 2) = _
    rw [quarter_inverse, hp, he]
    rfl
  · change movePermutation ((positiveMove a t).1, (positiveMove a t).2.1, 0) = _
    rw [hp, he]
    rfl
