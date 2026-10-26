import RubikSTM.Definitions.OBTM.Band.CleanAction
set_option autoImplicit false
open Rubik RubikConstruction.Control RubikOBTM.Band
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
theorem proof_RubikOBTM_Band_single_intersection_range {n : ℕ} (a d : Fin n)
    (ha : 1 ≤ a.val) (hd : 1 ≤ d.val) (has : 2*a.val+2 ≤ n)
    (hds : 2*d.val+2 ≤ n) (had : a ≠ d) (s : Sticker n) :
    (RubikBand.Band a s ∧ RubikBand.Band d s) ↔
    (s ∈ Set.range (plus a d) ∨ s ∈ Set.range (minus a d)) := by
  have han := a.isLt
  have hdn := d.isLt
  have hadv : a.val ≠ d.val := fun h => had (Fin.ext h)
  have d01 : low a ≠ high a := by
    intro he
    have hh := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at hh
    omega
  have d02 : low a ≠ a := by
    intro he
    have hh := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at hh
    omega
  have d03 : low a ≠ a.rev := by
    intro he
    have hh := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at hh
    omega
  have d04 : low a ≠ d := by
    intro he
    have hh := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at hh
    omega
  have d05 : low a ≠ d.rev := by
    intro he
    have hh := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at hh
    omega
  have d12 : high a ≠ a := by
    intro he
    have hh := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at hh
    omega
  have d13 : high a ≠ a.rev := by
    intro he
    have hh := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at hh
    omega
  have d14 : high a ≠ d := by
    intro he
    have hh := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at hh
    omega
  have d15 : high a ≠ d.rev := by
    intro he
    have hh := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at hh
    omega
  have d23 : a ≠ a.rev := by
    intro he
    have hh := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at hh
    omega
  have d24 : a ≠ d := by
    intro he
    have hh := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at hh
    omega
  have d25 : a ≠ d.rev := by
    intro he
    have hh := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at hh
    omega
  have d34 : a.rev ≠ d := by
    intro he
    have hh := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at hh
    omega
  have d35 : a.rev ≠ d.rev := by
    intro he
    have hh := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at hh
    omega
  have d45 : d ≠ d.rev := by
    intro he
    have hh := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at hh
    omega
  constructor
  · rintro ⟨hA,hD⟩
    rcases s with ⟨⟨⟨x,y,z⟩,q,b⟩,hs⟩
    fin_cases q <;> cases b
    · have hn : x = low a := by
        apply Fin.ext
        simpa [IsSurface, coordinate, low, high] using hs
      subst x
      simp [RubikBand.Band, Fin.exists_fin_succ, coordinate,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Fin.isValue, d01, Ne.symm d01, d02, Ne.symm d02, d03, Ne.symm d03, d04, Ne.symm d04, d05, Ne.symm d05, d12, Ne.symm d12, d13, Ne.symm d13, d14, Ne.symm d14, d15, Ne.symm d15, d23, Ne.symm d23, d24, Ne.symm d24, d25, Ne.symm d25, d34, Ne.symm d34, d35, Ne.symm d35, d45, Ne.symm d45, false_or, or_false, exists_const] at hA hD
      rcases hA with (hA|hA) | (hA|hA) <;>
        rcases hD with (hD|hD) | (hD|hD)
      · exact False.elim (d24 (hA.symm.trans hD))
      · exact False.elim (d25 (hA.symm.trans hD))
      · refine Or.inr ⟨(15 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inl ⟨(15 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · exact False.elim (d34 (hA.symm.trans hD))
      · exact False.elim (d35 (hA.symm.trans hD))
      · refine Or.inl ⟨(16 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inr ⟨(16 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inl ⟨(11 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inr ⟨(11 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · exact False.elim (d24 (hA.symm.trans hD))
      · exact False.elim (d25 (hA.symm.trans hD))
      · refine Or.inr ⟨(10 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inl ⟨(10 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · exact False.elim (d34 (hA.symm.trans hD))
      · exact False.elim (d35 (hA.symm.trans hD))
    · have hn : x = high a := by
        apply Fin.ext
        simpa [IsSurface, coordinate, low, high] using hs
      subst x
      simp [RubikBand.Band, Fin.exists_fin_succ, coordinate,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Fin.isValue, d01, Ne.symm d01, d02, Ne.symm d02, d03, Ne.symm d03, d04, Ne.symm d04, d05, Ne.symm d05, d12, Ne.symm d12, d13, Ne.symm d13, d14, Ne.symm d14, d15, Ne.symm d15, d23, Ne.symm d23, d24, Ne.symm d24, d25, Ne.symm d25, d34, Ne.symm d34, d35, Ne.symm d35, d45, Ne.symm d45, false_or, or_false, exists_const] at hA hD
      rcases hA with (hA|hA) | (hA|hA) <;>
        rcases hD with (hD|hD) | (hD|hD)
      · exact False.elim (d24 (hA.symm.trans hD))
      · exact False.elim (d25 (hA.symm.trans hD))
      · refine Or.inl ⟨(3 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inr ⟨(3 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · exact False.elim (d34 (hA.symm.trans hD))
      · exact False.elim (d35 (hA.symm.trans hD))
      · refine Or.inr ⟨(2 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inl ⟨(2 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inr ⟨(0 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inl ⟨(0 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · exact False.elim (d24 (hA.symm.trans hD))
      · exact False.elim (d25 (hA.symm.trans hD))
      · refine Or.inl ⟨(1 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inr ⟨(1 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · exact False.elim (d34 (hA.symm.trans hD))
      · exact False.elim (d35 (hA.symm.trans hD))
    · have hn : y = low a := by
        apply Fin.ext
        simpa [IsSurface, coordinate, low, high] using hs
      subst y
      simp [RubikBand.Band, Fin.exists_fin_succ, coordinate,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Fin.isValue, d01, Ne.symm d01, d02, Ne.symm d02, d03, Ne.symm d03, d04, Ne.symm d04, d05, Ne.symm d05, d12, Ne.symm d12, d13, Ne.symm d13, d14, Ne.symm d14, d15, Ne.symm d15, d23, Ne.symm d23, d24, Ne.symm d24, d25, Ne.symm d25, d34, Ne.symm d34, d35, Ne.symm d35, d45, Ne.symm d45, false_or, or_false, exists_const] at hA hD
      rcases hA with (hA|hA) | (hA|hA) <;>
        rcases hD with (hD|hD) | (hD|hD)
      · exact False.elim (d24 (hA.symm.trans hD))
      · exact False.elim (d25 (hA.symm.trans hD))
      · refine Or.inl ⟨(19 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inr ⟨(19 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · exact False.elim (d34 (hA.symm.trans hD))
      · exact False.elim (d35 (hA.symm.trans hD))
      · refine Or.inr ⟨(17 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inl ⟨(17 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inr ⟨(18 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inl ⟨(18 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · exact False.elim (d24 (hA.symm.trans hD))
      · exact False.elim (d25 (hA.symm.trans hD))
      · refine Or.inl ⟨(9 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inr ⟨(9 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · exact False.elim (d34 (hA.symm.trans hD))
      · exact False.elim (d35 (hA.symm.trans hD))
    · have hn : y = high a := by
        apply Fin.ext
        simpa [IsSurface, coordinate, low, high] using hs
      subst y
      simp [RubikBand.Band, Fin.exists_fin_succ, coordinate,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Fin.isValue, d01, Ne.symm d01, d02, Ne.symm d02, d03, Ne.symm d03, d04, Ne.symm d04, d05, Ne.symm d05, d12, Ne.symm d12, d13, Ne.symm d13, d14, Ne.symm d14, d15, Ne.symm d15, d23, Ne.symm d23, d24, Ne.symm d24, d25, Ne.symm d25, d34, Ne.symm d34, d35, Ne.symm d35, d45, Ne.symm d45, false_or, or_false, exists_const] at hA hD
      rcases hA with (hA|hA) | (hA|hA) <;>
        rcases hD with (hD|hD) | (hD|hD)
      · exact False.elim (d24 (hA.symm.trans hD))
      · exact False.elim (d25 (hA.symm.trans hD))
      · refine Or.inr ⟨(4 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inl ⟨(4 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · exact False.elim (d34 (hA.symm.trans hD))
      · exact False.elim (d35 (hA.symm.trans hD))
      · refine Or.inl ⟨(13 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inr ⟨(13 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inl ⟨(14 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inr ⟨(14 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · exact False.elim (d24 (hA.symm.trans hD))
      · exact False.elim (d25 (hA.symm.trans hD))
      · refine Or.inr ⟨(12 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inl ⟨(12 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · exact False.elim (d34 (hA.symm.trans hD))
      · exact False.elim (d35 (hA.symm.trans hD))
    · have hn : z = low a := by
        apply Fin.ext
        simpa [IsSurface, coordinate, low, high] using hs
      subst z
      simp [RubikBand.Band, Fin.exists_fin_succ, coordinate,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Fin.isValue, d01, Ne.symm d01, d02, Ne.symm d02, d03, Ne.symm d03, d04, Ne.symm d04, d05, Ne.symm d05, d12, Ne.symm d12, d13, Ne.symm d13, d14, Ne.symm d14, d15, Ne.symm d15, d23, Ne.symm d23, d24, Ne.symm d24, d25, Ne.symm d25, d34, Ne.symm d34, d35, Ne.symm d35, d45, Ne.symm d45, false_or, or_false, exists_const] at hA hD
      rcases hA with (hA|hA) | (hA|hA) <;>
        rcases hD with (hD|hD) | (hD|hD)
      · exact False.elim (d24 (hA.symm.trans hD))
      · exact False.elim (d25 (hA.symm.trans hD))
      · refine Or.inr ⟨(23 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inl ⟨(23 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · exact False.elim (d34 (hA.symm.trans hD))
      · exact False.elim (d35 (hA.symm.trans hD))
      · refine Or.inl ⟨(21 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inr ⟨(21 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inl ⟨(20 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inr ⟨(20 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · exact False.elim (d24 (hA.symm.trans hD))
      · exact False.elim (d25 (hA.symm.trans hD))
      · refine Or.inr ⟨(22 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inl ⟨(22 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · exact False.elim (d34 (hA.symm.trans hD))
      · exact False.elim (d35 (hA.symm.trans hD))
    · have hn : z = high a := by
        apply Fin.ext
        simpa [IsSurface, coordinate, low, high] using hs
      subst z
      simp [RubikBand.Band, Fin.exists_fin_succ, coordinate,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Fin.isValue, d01, Ne.symm d01, d02, Ne.symm d02, d03, Ne.symm d03, d04, Ne.symm d04, d05, Ne.symm d05, d12, Ne.symm d12, d13, Ne.symm d13, d14, Ne.symm d14, d15, Ne.symm d15, d23, Ne.symm d23, d24, Ne.symm d24, d25, Ne.symm d25, d34, Ne.symm d34, d35, Ne.symm d35, d45, Ne.symm d45, false_or, or_false, exists_const] at hA hD
      rcases hA with (hA|hA) | (hA|hA) <;>
        rcases hD with (hD|hD) | (hD|hD)
      · exact False.elim (d24 (hA.symm.trans hD))
      · exact False.elim (d25 (hA.symm.trans hD))
      · refine Or.inl ⟨(5 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inr ⟨(5 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · exact False.elim (d34 (hA.symm.trans hD))
      · exact False.elim (d35 (hA.symm.trans hD))
      · refine Or.inr ⟨(7 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inl ⟨(7 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inr ⟨(6 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inl ⟨(6 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · exact False.elim (d24 (hA.symm.trans hD))
      · exact False.elim (d25 (hA.symm.trans hD))
      · refine Or.inl ⟨(8 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · refine Or.inr ⟨(8 : Fin 24), ?_⟩
        apply Subtype.ext
        simpa [plus, minus, lab, rawLab, posTable, normalTable, hA, hD]
      · exact False.elim (d34 (hA.symm.trans hD))
      · exact False.elim (d35 (hA.symm.trans hD))

  · rintro (⟨i,rfl⟩ | ⟨i,rfl⟩) <;> fin_cases i <;>
      simp [RubikBand.Band, plus, minus, lab, rawLab, posTable, normalTable,
        Fin.exists_fin_succ, coordinate, low, high]
