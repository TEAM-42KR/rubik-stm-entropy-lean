import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
import RubikSTM.Definitions.Core.CoreAction
import RubikSTM.Lemmas.Wings.ReachableCleanup
import RubikSTM.Lemmas.Surface.DepthRegular
import RubikSTM.Lemmas.GlobalWords.Exceptional.CoreOutsideBand
import RubikSTM.Lemmas.GlobalWords.Exceptional.WingOutsideBand
import RubikSTM.Lemmas.GlobalWords.Exceptional.FixedWordColour
import RubikSTM.Lemmas.GlobalWords.Exceptional.FiniteCleanup
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open Rubik RubikGlobal RubikGlobalWord
open RubikGlobalWord.Exceptional
theorem proof_RubikGlobalWord_Exceptional_wings_cleanup : ∃ C : ℕ, ∀ (n : ℕ) (c : Position n),
    (∀ s : Sticker n, RubikCore.IsCore s → c.val s = solved n s) →
      ∃ w : List (Move n), w.length ≤ C * Fintype.card (I n) ∧
        (∀ s : Sticker n, RubikCore.IsCore s ∨ (∃ i : I n, s ∈ WingRange i) →
          applyWord w c.val s = solved n s) := by
  refine ⟨RubikWing.uniformCost, ?_⟩
  intro n c hcore
  let P : Set (Sticker n) := {s | RubikCore.IsCore s ∨ ∃ i : I n, s ∈ WingRange i}
  have hstep (i : I n) (d : Position n) : ∃ w : List (Move n),
      w.length ≤ RubikWing.uniformCost ∧ (∀ s ∈ WingRange i, applyWord w d.val s = solved n s) ∧
        (∀ s ∈ P, d.val s = solved n s → applyWord w d.val s = solved n s) := by
    obtain ⟨w, hw, _, hmatch, hoff⟩ := RubikWing.reachable_cleanup (depth_regular i).2 d
    have hR : ∀ s ∈ WingRange i, applyWord w d.val s = solved n s := by
      rintro s ⟨l, side, rfl⟩
      exact hmatch l side
    refine ⟨w, hw, hR, ?_⟩
    intro s hs hsol
    rcases hs with hcs | ⟨j, hjs⟩
    · exact (fixed_word_colour w d.val s (hoff s (core_outside_band i s hcs))).trans hsol
    · by_cases hij : i = j
      · subst j
        exact hR s hjs
      · exact (fixed_word_colour w d.val s (hoff s (wing_outside_band i j hij s hjs))).trans hsol
  obtain ⟨w, hw, hsol⟩ := finite_cleanup P WingRange RubikWing.uniformCost
    (fun i s hs => Or.inr ⟨i, hs⟩) hstep c
  refine ⟨w, hw, ?_⟩
  intro s hs
  apply hsol s
  rcases hs with hcs | hwing
  · exact Or.inl ⟨Or.inl hcs, hcore s hcs⟩
  · exact Or.inr hwing
