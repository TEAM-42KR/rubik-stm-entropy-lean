import RubikSTM.Definitions.Orbits.SwapPhi
import RubikSTM.Lemmas.Orbits.LabelBands
set_option autoImplicit false

theorem proof_RubikOrbit_bandIntersection {n : ℕ} {a b : Fin n} (hg : RubikGeometry.Generic n a b) (s : Rubik.Sticker n) :
  (RubikBand.Band a s ∧ RubikBand.Band b s) ↔
    s ∈ Set.range (RubikGeometry.lab a b) ∪ Set.range (RubikGeometry.lab b a) := by
  have ha := hg.one_le_a
  have hb0 := hg.one_le_b
  have haS := hg.a_small
  have hbS := hg.b_small
  have hab : a.val ≠ b.val := by
    intro h
    exact hg.ne (Fin.ext h)
  constructor
  · rintro ⟨haB, hbB⟩
    rcases haB with ⟨qa, haB⟩
    rcases hbB with ⟨qb, hbB⟩
    rcases s with ⟨⟨⟨x,y,z⟩,q,c⟩,hs⟩
    fin_cases q <;> cases c <;> fin_cases qa <;> fin_cases qb
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · refine Or.inr ⟨(11 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inl ⟨(15 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inl ⟨(16 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inr ⟨(10 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · refine Or.inl ⟨(11 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inr ⟨(16 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inr ⟨(15 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inl ⟨(10 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · refine Or.inl ⟨(3 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inr ⟨(1 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inr ⟨(0 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inl ⟨(2 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · refine Or.inr ⟨(3 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inl ⟨(0 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inl ⟨(1 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inr ⟨(2 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · refine Or.inl ⟨(19 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inr ⟨(9 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inr ⟨(18 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inl ⟨(17 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · refine Or.inr ⟨(19 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inl ⟨(18 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inl ⟨(9 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inr ⟨(17 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · refine Or.inr ⟨(14 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inl ⟨(4 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inl ⟨(13 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inr ⟨(12 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · refine Or.inl ⟨(14 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inr ⟨(13 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inr ⟨(4 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inl ⟨(12 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · refine Or.inr ⟨(20 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inl ⟨(23 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inl ⟨(21 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inr ⟨(22 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · refine Or.inl ⟨(20 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inr ⟨(21 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inr ⟨(23 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inl ⟨(22 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · refine Or.inl ⟨(5 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inr ⟨(8 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inr ⟨(6 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inl ⟨(7 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · refine Or.inr ⟨(5 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inl ⟨(6 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inl ⟨(8 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · refine Or.inr ⟨(7 : Fin 24), ?_⟩
        apply Subtype.ext
        simp [RubikGeometry.lab, RubikGeometry.rawLab, RubikGeometry.posTable, RubikGeometry.normalTable,
          RubikGeometry.lo, RubikGeometry.hi, Fin.ext_iff, Fin.rev]
        simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
    · dsimp [Rubik.coordinate, Rubik.IsSurface] at haB hbB hs
      rcases haB with haB | haB <;> rcases hbB with hbB | hbB
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
      · simp only [Fin.ext_iff, Fin.rev] at haB hbB
        omega
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact RubikOrbit.labelBands a b i
    · exact ⟨(RubikOrbit.labelBands b a i).2, (RubikOrbit.labelBands b a i).1⟩

#print axioms proof_RubikOrbit_bandIntersection
