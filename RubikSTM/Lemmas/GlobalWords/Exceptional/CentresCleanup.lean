import RubikSTM.Proofs.GlobalWords.Exceptional.CentresCleanup
import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
set_option autoImplicit false

theorem RubikGlobalWord.Exceptional.centres_cleanup :
    ∃ C : ℕ, ∀ (n : ℕ) (c : Rubik.Position n), ∃ w : List (Rubik.Move n), w.length ≤ C * (2 * Fintype.card (RubikGlobal.I n)) ∧ (∀ (i : RubikGlobal.I n) (s : Rubik.Sticker n), s ∈ RubikGlobal.DiagonalRange i ∨ s ∈ RubikGlobal.CrossRange i → Rubik.applyWord w c.val s = Rubik.solved n s) ∧ (∀ s, c.val s = Rubik.solved n s → Rubik.applyWord w c.val s = Rubik.solved n s) :=
  @proof_RubikGlobalWord_Exceptional_centres_cleanup
