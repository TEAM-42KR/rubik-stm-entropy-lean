import RubikSTM.Proofs.GlobalWords.FiniteGlobalWordBound
import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
import RubikSTM.Definitions.Core.CoreAction
set_option autoImplicit false

theorem RubikGlobalWord.finite_global_word_bound :
    ∃ C R : ℕ, ∀ (n h : ℕ) (f : RubikGlobal.I n → Fin h)
  (k M : RubikGlobalWord.GroupPair h → ℕ) (L : ℕ), 0 < L → 4 ∣ L →
  ∀ B : (p : RubikGlobalWord.GroupPair h) → RubikCodebook.Book RubikChannel.Paired.Letter (k p) L,
    (∀ p, 0 < k p) → (∀ p, RubikCodebook.CoversAll RubikChannel.Paired.act (B p)) →
    (∀ p (i : Fin L), ((B p) i).card ≤ M p) →
  ∀ c d : Rubik.Position n, ∃ w : List (Rubik.Move n),
    w.length ≤ (∑ p : RubikGlobalWord.GroupPair h, RubikGlobalWord.rectangleCost R f k M L p) +
      C*(RubikGlobalWord.sameCount f+6*Fintype.card (RubikGlobal.I n)) + 2*RubikCore.cleanupBound ∧
    Rubik.applyWord w c.val = d.val :=
  @proof_RubikGlobalWord_finite_global_word_bound
