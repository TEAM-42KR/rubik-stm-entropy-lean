import RubikSTM.Definitions.Surface.GenericRange
set_option autoImplicit false
open Rubik RubikGeometry RubikGlobal
open scoped Classical
set_option linter.unusedSimpArgs false

open RubikCore
private theorem RubikCore.isLevel_rev {n : ℕ} (x : Fin n) : IsLevel x.rev ↔ IsLevel x := by
  have h {y : Fin n} : IsLevel y → IsLevel y.rev := by
    intro hy
    rcases hy with h0 | h1 | hm
    · right; left
      simp [Fin.rev, h0]
    · left
      simp only [Fin.rev, h1]
      omega
    · right; right
      rw [Fin.rev_rev]
      exact hm.symm
  exact ⟨fun hh => by simpa using h hh, h⟩

private theorem RubikGlobal.nonlevel_half_depth {n : ℕ} (x : Fin n) (hx : ¬ RubikCore.IsLevel x) :
    ∃ a : Fin n, RubikExceptional.Regular n a ∧ (x = a ∨ x = a.rev) := by
  have hn := x.isLt
  have hx0 : x.val ≠ 0 := fun h => hx (Or.inl h)
  have hxhi : x.val ≠ n - 1 := fun h => hx (Or.inr (Or.inl h))
  have hxmid : x.rev ≠ x := fun h => hx (Or.inr (Or.inr h))
  have hv : n - (x.val + 1) ≠ x.val := by
    intro h
    apply hxmid
    exact Fin.ext h
  by_cases hs : 2 * x.val + 2 ≤ n
  · exact ⟨x, ⟨by omega, hs⟩, Or.inl rfl⟩
  · refine ⟨x.rev, ⟨?_, ?_⟩, Or.inr (Fin.rev_rev x).symm⟩
    · change 1 ≤ n - (x.val + 1)
      omega
    · change 2 * (n - (x.val + 1)) + 2 ≤ n
      omega

private theorem RubikGlobal.regular_index {n : ℕ} (a : Fin n) (ha : RubikExceptional.Regular n a) :
    ∃ i : RubikGlobal.I n, RubikGlobal.depth i = a := by
  have hpos := ha.positive
  have hs := ha.small
  refine ⟨⟨a.val - 1, by omega⟩, ?_⟩
  apply Fin.ext
  change a.val - 1 + 1 = a.val
  omega

private theorem RubikGlobal.centre_chart_cover {n : ℕ} (a b : Fin n) (s : Rubik.Sticker n)
    (h : RubikGlobal.CentreFrame a b s) :
    s ∈ Set.range (RubikGeometry.lab a b) ∪ Set.range (RubikGeometry.lab b a) := by
  rcases s with ⟨⟨⟨x,y,z⟩,axis,sign⟩,hs⟩
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
  have ha := a.isLt
  have hb := b.isLt
  fin_cases axis
  · cases sign
    · simp [Rubik.IsSurface, Rubik.coordinate] at hs
      simp [RubikGlobal.CentreFrame, RubikGlobal.tangent] at h
      rcases h with (⟨hu | hu, hv | hv⟩ | ⟨hu | hu, hv | hv⟩)
      · refine Or.inl ⟨(15 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inr ⟨(11 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inr ⟨(10 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inl ⟨(16 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inr ⟨(15 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inl ⟨(11 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inl ⟨(10 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inr ⟨(16 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
    · simp [Rubik.IsSurface, Rubik.coordinate] at hs
      simp [RubikGlobal.CentreFrame, RubikGlobal.tangent] at h
      rcases h with (⟨hu | hu, hv | hv⟩ | ⟨hu | hu, hv | hv⟩)
      · refine Or.inl ⟨(3 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inr ⟨(1 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inr ⟨(0 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inl ⟨(2 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inr ⟨(3 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inl ⟨(1 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inl ⟨(0 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inr ⟨(2 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
  · cases sign
    · simp [Rubik.IsSurface, Rubik.coordinate] at hs
      simp [RubikGlobal.CentreFrame, RubikGlobal.tangent] at h
      rcases h with (⟨hu | hu, hv | hv⟩ | ⟨hu | hu, hv | hv⟩)
      · refine Or.inl ⟨(19 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inr ⟨(9 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inr ⟨(18 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inl ⟨(17 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inr ⟨(19 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inl ⟨(9 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inl ⟨(18 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inr ⟨(17 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
    · simp [Rubik.IsSurface, Rubik.coordinate] at hs
      simp [RubikGlobal.CentreFrame, RubikGlobal.tangent] at h
      rcases h with (⟨hu | hu, hv | hv⟩ | ⟨hu | hu, hv | hv⟩)
      · refine Or.inl ⟨(4 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inr ⟨(14 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inr ⟨(12 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inl ⟨(13 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inr ⟨(4 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inl ⟨(14 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inl ⟨(12 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inr ⟨(13 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
  · cases sign
    · simp [Rubik.IsSurface, Rubik.coordinate] at hs
      simp [RubikGlobal.CentreFrame, RubikGlobal.tangent] at h
      rcases h with (⟨hu | hu, hv | hv⟩ | ⟨hu | hu, hv | hv⟩)
      · refine Or.inl ⟨(20 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inr ⟨(21 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inr ⟨(23 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inl ⟨(22 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inr ⟨(20 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inl ⟨(21 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inl ⟨(23 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inr ⟨(22 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
    · simp [Rubik.IsSurface, Rubik.coordinate] at hs
      simp [RubikGlobal.CentreFrame, RubikGlobal.tangent] at h
      rcases h with (⟨hu | hu, hv | hv⟩ | ⟨hu | hu, hv | hv⟩)
      · refine Or.inl ⟨(5 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inr ⟨(8 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inr ⟨(6 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inl ⟨(7 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inr ⟨(5 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inl ⟨(8 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inl ⟨(6 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega
      · refine Or.inr ⟨(7 : Fin 24), ?_⟩
        have huu := congrArg Fin.val hu
        have hvv := congrArg Fin.val hv
        try simp only [Fin.val_rev] at huu hvv
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable,
          RubikGeometry.normalTable, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff,
          Fin.val_rev] <;> omega

private theorem RubikGlobal.wing_chart_cover {n : ℕ} (a : Fin n) (s : Rubik.Sticker n)
    (h : RubikGlobal.WingFrame a s) :
    ∃ i : Fin 24, ∃ b : Fin 2, RubikWing.lab a i b = s := by
  rcases s with ⟨⟨⟨x,y,z⟩,axis,sign⟩,hs⟩
  have hx := x.isLt
  have hy := y.isLt
  have hz := z.isLt
  have ha := a.isLt
  fin_cases axis
  · cases sign
    · simp [Rubik.IsSurface, Rubik.coordinate] at hs
      simp [RubikGlobal.WingFrame, RubikGlobal.tangent] at h
      rcases h with (⟨hu | hu, hv | hv⟩ | ⟨hu | hu, hv | hv⟩)
      · refine ⟨(1 : Fin 24), (1 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(0 : Fin 24), (0 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(7 : Fin 24), (0 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(6 : Fin 24), (1 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(3 : Fin 24), (0 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(2 : Fin 24), (1 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(5 : Fin 24), (1 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(4 : Fin 24), (0 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
    · simp [Rubik.IsSurface, Rubik.coordinate] at hs
      simp [RubikGlobal.WingFrame, RubikGlobal.tangent] at h
      rcases h with (⟨hu | hu, hv | hv⟩ | ⟨hu | hu, hv | hv⟩)
      · refine ⟨(16 : Fin 24), (1 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(17 : Fin 24), (0 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(22 : Fin 24), (0 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(23 : Fin 24), (1 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(18 : Fin 24), (0 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(19 : Fin 24), (1 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(20 : Fin 24), (1 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(21 : Fin 24), (0 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
  · cases sign
    · simp [Rubik.IsSurface, Rubik.coordinate] at hs
      simp [RubikGlobal.WingFrame, RubikGlobal.tangent] at h
      rcases h with (⟨hu | hu, hv | hv⟩ | ⟨hu | hu, hv | hv⟩)
      · refine ⟨(0 : Fin 24), (1 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(1 : Fin 24), (0 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(16 : Fin 24), (0 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(17 : Fin 24), (1 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(8 : Fin 24), (0 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(9 : Fin 24), (1 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(12 : Fin 24), (1 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(13 : Fin 24), (0 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
    · simp [Rubik.IsSurface, Rubik.coordinate] at hs
      simp [RubikGlobal.WingFrame, RubikGlobal.tangent] at h
      rcases h with (⟨hu | hu, hv | hv⟩ | ⟨hu | hu, hv | hv⟩)
      · refine ⟨(7 : Fin 24), (1 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(6 : Fin 24), (0 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(23 : Fin 24), (0 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(22 : Fin 24), (1 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(11 : Fin 24), (0 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(10 : Fin 24), (1 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(15 : Fin 24), (1 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(14 : Fin 24), (0 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
  · cases sign
    · simp [Rubik.IsSurface, Rubik.coordinate] at hs
      simp [RubikGlobal.WingFrame, RubikGlobal.tangent] at h
      rcases h with (⟨hu | hu, hv | hv⟩ | ⟨hu | hu, hv | hv⟩)
      · refine ⟨(8 : Fin 24), (1 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(12 : Fin 24), (0 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(10 : Fin 24), (0 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(14 : Fin 24), (1 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(2 : Fin 24), (0 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(18 : Fin 24), (1 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(4 : Fin 24), (1 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(20 : Fin 24), (0 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
    · simp [Rubik.IsSurface, Rubik.coordinate] at hs
      simp [RubikGlobal.WingFrame, RubikGlobal.tangent] at h
      rcases h with (⟨hu | hu, hv | hv⟩ | ⟨hu | hu, hv | hv⟩)
      · refine ⟨(3 : Fin 24), (1 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(5 : Fin 24), (0 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(19 : Fin 24), (0 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(21 : Fin 24), (1 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(9 : Fin 24), (0 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(11 : Fin 24), (1 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(13 : Fin 24), (1 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega
      · refine ⟨(15 : Fin 24), (0 : Fin 2), ?_⟩
        try simp only [Fin.ext_iff, Fin.val_rev] at hu hv
        apply Subtype.ext
        simp [RubikWing.lab, RubikWing.pos, RubikWing.normal,
          RubikWing.lo, RubikWing.hi, Fin.ext_iff, Fin.val_rev] <;> omega

private theorem RubikGlobal.core_tangent_iff {n : ℕ} (s : Rubik.Sticker n) :
    RubikCore.IsCore s ↔ RubikCore.IsLevel (RubikGlobal.tangent s.val).1 ∧
      RubikCore.IsLevel (RubikGlobal.tangent s.val).2 := by
  rcases s with ⟨⟨⟨x,y,z⟩,axis,sign⟩,hs⟩
  fin_cases axis
  · cases sign
    · simp [Rubik.IsSurface, Rubik.coordinate] at hs
      have hb : RubikCore.IsLevel x := Or.inl hs
      simp [RubikCore.IsCore, Fin.forall_fin_succ, Rubik.coordinate,
        RubikGlobal.tangent, RubikCore.isLevel_rev, hb, and_comm, and_left_comm, and_assoc]
    · simp [Rubik.IsSurface, Rubik.coordinate] at hs
      have hb : RubikCore.IsLevel x := Or.inr (Or.inl hs)
      simp [RubikCore.IsCore, Fin.forall_fin_succ, Rubik.coordinate,
        RubikGlobal.tangent, RubikCore.isLevel_rev, hb, and_comm, and_left_comm, and_assoc]
  · cases sign
    · simp [Rubik.IsSurface, Rubik.coordinate] at hs
      have hb : RubikCore.IsLevel y := Or.inl hs
      simp [RubikCore.IsCore, Fin.forall_fin_succ, Rubik.coordinate,
        RubikGlobal.tangent, RubikCore.isLevel_rev, hb, and_comm, and_left_comm, and_assoc]
    · simp [Rubik.IsSurface, Rubik.coordinate] at hs
      have hb : RubikCore.IsLevel y := Or.inr (Or.inl hs)
      simp [RubikCore.IsCore, Fin.forall_fin_succ, Rubik.coordinate,
        RubikGlobal.tangent, RubikCore.isLevel_rev, hb, and_comm, and_left_comm, and_assoc]
  · cases sign
    · simp [Rubik.IsSurface, Rubik.coordinate] at hs
      have hb : RubikCore.IsLevel z := Or.inl hs
      simp [RubikCore.IsCore, Fin.forall_fin_succ, Rubik.coordinate,
        RubikGlobal.tangent, RubikCore.isLevel_rev, hb, and_comm, and_left_comm, and_assoc]
    · simp [Rubik.IsSurface, Rubik.coordinate] at hs
      have hb : RubikCore.IsLevel z := Or.inr (Or.inl hs)
      simp [RubikCore.IsCore, Fin.forall_fin_succ, Rubik.coordinate,
        RubikGlobal.tangent, RubikCore.isLevel_rev, hb, and_comm, and_left_comm, and_assoc]

private theorem RubikGlobal.cross_swap_range {n : ℕ} (a m : Fin n) (hm : m.rev = m) :
    Set.range (RubikGeometry.lab m a) = Set.range (RubikGeometry.lab a m) := by
  ext s
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · refine ⟨(2 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(3 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(1 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(0 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(12 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(6 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(7 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(8 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(5 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(19 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(16 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(15 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(13 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(14 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(4 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(10 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(11 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(9 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(17 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(18 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(23 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(20 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(21 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(22 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
  · rintro ⟨i, rfl⟩
    fin_cases i
    · refine ⟨(3 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(2 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(0 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(1 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(14 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(8 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(5 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(6 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(7 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(17 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(15 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(16 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(4 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(12 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(13 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(11 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(10 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(18 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(19 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(9 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(21 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(22 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(23 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]
    · refine ⟨(20 : Fin 24), ?_⟩
      apply Subtype.ext
      simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
        hm, RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff]

theorem proof_RubikGlobal_surface_cover {n : ℕ} (s : Rubik.Sticker n) :
    RubikCore.IsCore s ∨ (∃ i : RubikGlobal.I n, s ∈ RubikGlobal.WingRange i) ∨
    (∃ i : RubikGlobal.I n, s ∈ RubikGlobal.DiagonalRange i) ∨
    (∃ i : RubikGlobal.I n, s ∈ RubikGlobal.CrossRange i) ∨
    (∃ p : RubikGlobal.Q n, s ∈ RubikGlobal.GenericRange p) := by
  classical
  let R : Prop := (∃ i : RubikGlobal.I n, s ∈ RubikGlobal.WingRange i) ∨
    (∃ i : RubikGlobal.I n, s ∈ RubikGlobal.DiagonalRange i) ∨
    (∃ i : RubikGlobal.I n, s ∈ RubikGlobal.CrossRange i) ∨
    (∃ p : RubikGlobal.Q n, s ∈ RubikGlobal.GenericRange p)
  have hwing (a : Fin n) (ha : RubikExceptional.Regular n a)
      (hf : RubikGlobal.WingFrame a s) : R := by
    obtain ⟨i, hi⟩ := RubikGlobal.regular_index a ha
    obtain ⟨l, b, hb⟩ := RubikGlobal.wing_chart_cover a s hf
    refine Or.inl ⟨i, l, b, ?_⟩
    simpa only [hi] using hb
  have hcross (a m : Fin n) (ha : RubikExceptional.Regular n a)
      (hm : m.rev = m) (hf : RubikGlobal.CentreFrame a m s) : R := by
    obtain ⟨i, hi⟩ := RubikGlobal.regular_index a ha
    have hr : s ∈ Set.range (RubikGeometry.lab a m) := by
      rcases RubikGlobal.centre_chart_cover a m s hf with h | h
      · exact h
      · rw [RubikGlobal.cross_swap_range a m hm] at h
        exact h
    refine Or.inr (Or.inr (Or.inl ⟨i, m, hm, ?_⟩))
    simpa only [hi] using hr
  have hregular (a b : Fin n) (ha : RubikExceptional.Regular n a)
      (hb : RubikExceptional.Regular n b) (hf : RubikGlobal.CentreFrame a b s) : R := by
    obtain ⟨i, hi⟩ := RubikGlobal.regular_index a ha
    obtain ⟨j, hj⟩ := RubikGlobal.regular_index b hb
    have hr := RubikGlobal.centre_chart_cover a b s hf
    by_cases hab : a = b
    · rcases hab with rfl
      refine Or.inr (Or.inl ⟨i, ?_⟩)
      change s ∈ Set.range (RubikGeometry.lab (RubikGlobal.depth i) (RubikGlobal.depth i))
      rw [hi]
      exact hr.elim id id
    · have hij : i ≠ j := by
        intro h
        exact hab (hi.symm.trans ((congrArg RubikGlobal.depth h).trans hj))
      rcases hr with hr | hr
      · refine Or.inr (Or.inr (Or.inr ⟨⟨(i,j), hij⟩, ?_⟩))
        change s ∈ Set.range (RubikGeometry.lab (RubikGlobal.depth i) (RubikGlobal.depth j))
        simpa only [hi, hj] using hr
      · refine Or.inr (Or.inr (Or.inr ⟨⟨(j,i), Ne.symm hij⟩, ?_⟩))
        change s ∈ Set.range (RubikGeometry.lab (RubikGlobal.depth j) (RubikGlobal.depth i))
        simpa only [hi, hj] using hr
  by_cases hcore : RubikCore.IsCore s
  · exact Or.inl hcore
  right
  change R
  let u := (RubikGlobal.tangent s.val).1
  let v := (RubikGlobal.tangent s.val).2
  have hn : ¬ (RubikCore.IsLevel u ∧ RubikCore.IsLevel v) :=
    mt (RubikGlobal.core_tangent_iff s).mpr hcore
  by_cases hu : RubikCore.IsLevel u
  · have hv : ¬ RubikCore.IsLevel v := fun hv => hn ⟨hu, hv⟩
    obtain ⟨a, ha, hva⟩ := RubikGlobal.nonlevel_half_depth v hv
    rcases hu with h0 | hhi | hm
    · exact hwing a ha (Or.inl ⟨Or.inl h0, hva⟩)
    · exact hwing a ha (Or.inl ⟨Or.inr hhi, hva⟩)
    · exact hcross a u ha hm (Or.inr ⟨Or.inl rfl, hva⟩)
  · obtain ⟨a, ha, hua⟩ := RubikGlobal.nonlevel_half_depth u hu
    by_cases hv : RubikCore.IsLevel v
    · rcases hv with h0 | hhi | hm
      · exact hwing a ha (Or.inr ⟨hua, Or.inl h0⟩)
      · exact hwing a ha (Or.inr ⟨hua, Or.inr hhi⟩)
      · exact hcross a v ha hm (Or.inl ⟨hua, Or.inl rfl⟩)
    · obtain ⟨b, hb, hvb⟩ := RubikGlobal.nonlevel_half_depth v hv
      exact hregular a b ha hb (Or.inl ⟨hua, hvb⟩)

#print axioms proof_RubikGlobal_surface_cover
