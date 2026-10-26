import RubikSTM.Proofs.GlobalWords.Exceptional.FiniteCleanup
import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
set_option autoImplicit false

theorem RubikGlobalWord.Exceptional.finite_cleanup :
    ∀ {n : ℕ} {E : Type*} [Fintype E] (P : Set (Rubik.Sticker n)) (R : E → Set (Rubik.Sticker n)) (C : ℕ) (hR : ∀ e, R e ⊆ P) (hstep : ∀ (e : E) (c : Rubik.Position n), ∃ w : List (Rubik.Move n), w.length ≤ C ∧ (∀ s ∈ R e, Rubik.applyWord w c.val s = Rubik.solved n s) ∧ (∀ s ∈ P, c.val s = Rubik.solved n s → Rubik.applyWord w c.val s = Rubik.solved n s)) (c : Rubik.Position n), ∃ w : List (Rubik.Move n), w.length ≤ C * Fintype.card E ∧ ∀ s, ((s ∈ P ∧ c.val s = Rubik.solved n s) ∨ ∃ e, s ∈ R e) → Rubik.applyWord w c.val s = Rubik.solved n s :=
  @proof_RubikGlobalWord_Exceptional_finite_cleanup
