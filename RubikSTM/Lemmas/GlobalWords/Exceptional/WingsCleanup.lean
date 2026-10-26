import RubikSTM.Proofs.GlobalWords.Exceptional.WingsCleanup
import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
set_option autoImplicit false

theorem RubikGlobalWord.Exceptional.wings_cleanup :
    ∃ C : ℕ, ∀ (n : ℕ) (c : Rubik.Position n), (∀ s : Rubik.Sticker n, RubikCore.IsCore s → c.val s = Rubik.solved n s) → ∃ w : List (Rubik.Move n), w.length ≤ C * Fintype.card (RubikGlobal.I n) ∧ (∀ s : Rubik.Sticker n, RubikCore.IsCore s ∨ (∃ i : RubikGlobal.I n, s ∈ RubikGlobal.WingRange i) → Rubik.applyWord w c.val s = Rubik.solved n s) :=
  @proof_RubikGlobalWord_Exceptional_wings_cleanup
