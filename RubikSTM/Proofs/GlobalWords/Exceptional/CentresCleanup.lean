import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
import RubikSTM.Definitions.Core.CoreAction
import RubikSTM.Lemmas.GlobalWords.Exceptional.CentreStep
import RubikSTM.Lemmas.GlobalWords.Exceptional.FiniteCleanup
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open Rubik RubikGlobal RubikGlobalWord
open RubikGlobalWord.Exceptional
theorem proof_RubikGlobalWord_Exceptional_centres_cleanup : ∃ C : ℕ, ∀ (n : ℕ) (c : Position n),
    ∃ w : List (Move n), w.length ≤ C * (2 * Fintype.card (I n)) ∧
      (∀ (i : I n) (s : Sticker n), s ∈ DiagonalRange i ∨ s ∈ CrossRange i →
        applyWord w c.val s = solved n s) ∧
      (∀ s, c.val s = solved n s → applyWord w c.val s = solved n s) := by
  obtain ⟨C, hC⟩ := centre_step
  refine ⟨C, ?_⟩
  intro n c
  let R : (I n × Fin 2) → Set (Sticker n) := fun p =>
    if p.2 = 0 then DiagonalRange p.1 else CrossRange p.1
  have hstep : ∀ (p : I n × Fin 2) (d : Position n), ∃ w : List (Move n),
      w.length ≤ C ∧ (∀ s ∈ R p, applyWord w d.val s = solved n s) ∧
        (∀ s ∈ Set.univ, d.val s = solved n s → applyWord w d.val s = solved n s) := by
    intro p d
    obtain ⟨w, hw, hr, hm⟩ := hC n p.1 p.2 d
    exact ⟨w, hw, hr, fun s _ hs => hm s hs⟩
  obtain ⟨w, hw, hs⟩ := finite_cleanup Set.univ R C (fun _ _ _ => trivial) hstep c
  refine ⟨w, ?_, ?_, ?_⟩
  · simpa [Fintype.card_prod, Nat.mul_comm] using hw
  · intro i s h
    apply hs s
    rcases h with h | h
    · exact Or.inr ⟨(i, 0), by simpa [R] using h⟩
    · exact Or.inr ⟨(i, 1), by simpa [R] using h⟩
  · intro s h
    exact hs s (Or.inl ⟨trivial, h⟩)
