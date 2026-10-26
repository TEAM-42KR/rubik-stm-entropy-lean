import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
import RubikSTM.Definitions.Core.CoreAction
import RubikSTM.Lemmas.GlobalWords.Exceptional.WingsCleanup
import RubikSTM.Lemmas.GlobalWords.Exceptional.CentresCleanup
import RubikSTM.Lemmas.Core.CleanupToSolved
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open Rubik RubikGlobal RubikGlobalWord
open RubikGlobalWord.Exceptional
theorem proof_RubikGlobalWord_exceptional_preprocessing : ∃ C : ℕ, ∀ (n : ℕ) (c : Position n),
    ∃ w : List (Move n),
      w.length ≤ RubikCore.cleanupBound + C * (3 * Fintype.card (I n)) ∧
      ∀ s : Sticker n, Nongeneric s → applyWord w c.val s = solved n s := by
  obtain ⟨W, hW⟩ := wings_cleanup
  obtain ⟨E, hE⟩ := centres_cleanup
  refine ⟨W + E, ?_⟩
  intro n c
  obtain ⟨u, hu, hcore⟩ := RubikCore.cleanup_to_solved c
  obtain ⟨v, hv, hwing⟩ := hW n (advance c u) hcore
  obtain ⟨z, hz, hcentre, hkeep⟩ := hE n (advance (advance c u) v)
  have happ (p q : List (Move n)) (d : Colouring n) :
      applyWord (p ++ q) d = applyWord q (applyWord p d) := by
    simp only [applyWord, List.foldl_append]
  refine ⟨u ++ v ++ z, ?_, ?_⟩
  · simp only [List.length_append]
    calc
      u.length + v.length + z.length ≤
          RubikCore.cleanupBound + W * Fintype.card (I n) + E * (2 * Fintype.card (I n)) :=
        Nat.add_le_add (Nat.add_le_add hu hv) hz
      _ ≤ RubikCore.cleanupBound + (W + E) * (3 * Fintype.card (I n)) := by nlinarith
  · intro s hs
    rw [happ, happ]
    change applyWord z (advance (advance c u) v).val s = solved n s
    rcases hs with hcs | ⟨⟨i, k⟩, he⟩
    · exact hkeep s (hwing s (Or.inl hcs))
    · fin_cases k
      · have hws : s ∈ WingRange i := by simpa [ExceptionalRange] using he
        exact hkeep s (hwing s (Or.inr ⟨i, hws⟩))
      · have hds : s ∈ DiagonalRange i := by simpa [ExceptionalRange] using he
        exact hcentre i s (Or.inl hds)
      · have hxs : s ∈ CrossRange i := by simpa [ExceptionalRange] using he
        exact hcentre i s (Or.inr hxs)
