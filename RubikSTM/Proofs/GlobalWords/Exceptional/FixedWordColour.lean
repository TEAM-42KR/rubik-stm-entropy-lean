import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
import RubikSTM.Definitions.Core.CoreAction
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open Rubik RubikGlobal RubikGlobalWord
theorem proof_RubikGlobalWord_Exceptional_fixed_word_colour {n : ℕ} (w : List (Move n)) (c : Colouring n)
    (s : Sticker n) (h : RubikBand.wordPerm w s = s) : applyWord w c s = c s := by
  have heval (u : List (Move n)) (d : Colouring n) :
      applyWord u d = fun t => d ((RubikBand.wordPerm u)⁻¹ t) := by
    induction u generalizing d with
    | nil => rfl
    | cons m u ih =>
      change applyWord u (applyMove m d) = _
      rw [ih]
      funext t
      simp [RubikBand.wordPerm, applyMove]
  have hinv : (RubikBand.wordPerm w)⁻¹ s = s := by
    rw [Equiv.Perm.inv_eq_iff_eq, h]
  simpa only [hinv] using congrFun (heval w c) s
