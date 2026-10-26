import RubikSTM.Proofs.GlobalWords.Exceptional.CentreStep
import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
set_option autoImplicit false

theorem RubikGlobalWord.Exceptional.centre_step :
    ∃ C : ℕ, ∀ (n : ℕ) (i : RubikGlobal.I n) (k : Fin 2) (c : Rubik.Position n), ∃ w : List (Rubik.Move n), w.length ≤ C ∧ (∀ s ∈ (if k = 0 then RubikGlobal.DiagonalRange i else RubikGlobal.CrossRange i), Rubik.applyWord w c.val s = Rubik.solved n s) ∧ (∀ s, c.val s = Rubik.solved n s → Rubik.applyWord w c.val s = Rubik.solved n s) :=
  @proof_RubikGlobalWord_Exceptional_centre_step
