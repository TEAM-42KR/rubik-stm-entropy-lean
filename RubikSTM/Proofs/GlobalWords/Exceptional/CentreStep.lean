import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
import RubikSTM.Definitions.Core.CoreAction
import RubikSTM.Lemmas.ExceptionalCentres.DiagonalUniformColoured
import RubikSTM.Lemmas.ExceptionalCentres.CrossUniformColoured
import RubikSTM.Lemmas.Surface.DepthRegular
import RubikSTM.Lemmas.GlobalWords.Exceptional.FixedWordColour
import RubikSTM.Lemmas.GlobalWords.Exceptional.MidpointUnique
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open Rubik RubikGlobal RubikGlobalWord
open RubikGlobalWord.Exceptional
theorem proof_RubikGlobalWord_Exceptional_centre_step : ∃ C : ℕ, ∀ (n : ℕ) (i : I n) (k : Fin 2) (c : Position n),
    ∃ w : List (Move n), w.length ≤ C ∧
      (∀ s ∈ (if k = 0 then DiagonalRange i else CrossRange i), applyWord w c.val s = solved n s) ∧
      (∀ s, c.val s = solved n s → applyWord w c.val s = solved n s) := by
  classical
  obtain ⟨D, hD⟩ := RubikExceptional.DiagonalUniformColoured
  obtain ⟨X, hX⟩ := RubikExceptional.CrossUniformColoured
  refine ⟨D + X, ?_⟩
  intro n i k c
  have hsol : Reachable (solved n) := ⟨[], rfl⟩
  fin_cases k
  · obtain ⟨w, hw, hmatch, hoff⟩ := hD n (depth i) (depth_regular i).1 c.val (solved n) c.property hsol
    have hR : ∀ s ∈ DiagonalRange i, applyWord w c.val s = solved n s := by
      rintro s ⟨l, rfl⟩
      exact hmatch l
    refine ⟨w, hw.trans (Nat.le_add_right D X), ?_, ?_⟩
    · simpa using hR
    · intro s hs
      by_cases hr : s ∈ DiagonalRange i
      · exact hR s hr
      · have hf : RubikBand.wordPerm w s = s := hoff s hr
        exact (fixed_word_colour w c.val s hf).trans hs
  · by_cases hex : ∃ m : Fin n, m.rev = m
    · obtain ⟨m, hm⟩ := hex
      obtain ⟨w, hw, hmatch, hoff⟩ := hX n (depth i) m (depth_regular i).1 hm c.val (solved n) c.property hsol
      have hR : ∀ s ∈ CrossRange i, applyWord w c.val s = solved n s := by
        rintro s ⟨m', hm', l, hl⟩
        have he := midpoint_unique m' m hm' hm
        subst m'
        rw [← hl]
        exact hmatch l
      refine ⟨w, hw.trans (Nat.le_add_left X D), ?_, ?_⟩
      · simpa using hR
      · intro s hs
        by_cases hr : s ∈ Set.range (RubikGeometry.lab (depth i) m)
        · obtain ⟨l, rfl⟩ := hr
          exact hmatch l
        · have hf : RubikBand.wordPerm w s = s := hoff s hr
          exact (fixed_word_colour w c.val s hf).trans hs
    · refine ⟨[], by simp, ?_, ?_⟩
      · intro s hs
        change s ∈ CrossRange i at hs
        obtain ⟨m, hm, _⟩ := hs
        exact (hex ⟨m, hm⟩).elim
      · intro s hs
        exact hs
