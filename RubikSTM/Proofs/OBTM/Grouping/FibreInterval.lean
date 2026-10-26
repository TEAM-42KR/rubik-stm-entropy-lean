import RubikSTM.Definitions.OBTM.Grouping.GroupOf
import RubikSTM.Lemmas.OBTM.Grouping.GroupOfMonotone
set_option autoImplicit false

theorem proof_RubikOBTM_Grouping_fibre_interval (m h : ℕ) (hh : 0 < h) (t : Fin h)
    (hg : (RubikOBTM.Grouping.group m h hh t).Nonempty) :
    RubikOBTM.Grouping.positiveGroup m h hh t =
      Finset.Icc (RubikOBTM.Grouping.lower m h hh t hg) (RubikOBTM.Grouping.upper m h hh t hg) ∧
    1 ≤ RubikOBTM.Grouping.lower m h hh t hg ∧
    RubikOBTM.Grouping.lower m h hh t hg ≤ RubikOBTM.Grouping.upper m h hh t hg ∧
    RubikOBTM.Grouping.upper m h hh t hg ≤ m := by
  classical
  let S := RubikOBTM.Grouping.group m h hh t
  let lo := S.min' hg
  let hi := S.max' hg
  have hlo : RubikOBTM.Grouping.groupOf m h hh lo = t := by
    exact (Finset.mem_filter.mp (S.min'_mem hg)).2
  have hhi : RubikOBTM.Grouping.groupOf m h hh hi = t := by
    exact (Finset.mem_filter.mp (S.max'_mem hg)).2
  have hinterval (i : Fin m) : i ∈ S ↔ lo ≤ i ∧ i ≤ hi := by
    constructor
    · intro hiS
      exact ⟨S.min'_le _ hiS, S.le_max' _ hiS⟩
    · rintro ⟨hloi, hihi⟩
      have h₁ := RubikOBTM.Grouping.groupOf_monotone m h hh hloi
      have h₂ := RubikOBTM.Grouping.groupOf_monotone m h hh hihi
      have he : RubikOBTM.Grouping.groupOf m h hh i = t := by
        rw [hlo] at h₁
        rw [hhi] at h₂
        exact le_antisymm h₂ h₁
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩
  change RubikOBTM.Grouping.positiveGroup m h hh t = Finset.Icc (lo.val + 1) (hi.val + 1) ∧
    1 ≤ lo.val + 1 ∧ lo.val + 1 ≤ hi.val + 1 ∧ hi.val + 1 ≤ m
  refine ⟨?_, by omega, ?_, by have := hi.isLt; omega⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨i, his, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hli, hih⟩ := (hinterval i).mp his
      apply Finset.mem_Icc.mpr
      change lo.val ≤ i.val at hli
      change i.val ≤ hi.val at hih
      omega
    · intro hx
      obtain ⟨hlx, hxh⟩ := Finset.mem_Icc.mp hx
      let i : Fin m := ⟨x - 1, by have := hi.isLt; omega⟩
      have hiS : i ∈ S := (hinterval i).mpr (by
        change lo.val ≤ x - 1 ∧ x - 1 ≤ hi.val
        omega)
      apply Finset.mem_image.mpr
      exact ⟨i, hiS, by dsimp [i]; omega⟩
  · have he : lo ≤ hi := S.min'_le_max' hg
    change lo.val ≤ hi.val at he
    omega
