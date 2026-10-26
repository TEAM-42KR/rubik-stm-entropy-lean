import RubikSTM.Definitions.Wings.IsMiddleSkeleton
set_option autoImplicit false
open Rubik RubikWing
set_option linter.unusedSimpArgs false

private theorem RubikWing.arbitrary_quarter_action {n : ℕ} {c : Fin n} (hc : Admissible n c)
    (a : Axis) (l : Fin n) : ∃ σ : Equiv.Perm Label,
    ∀ i b, sliceQuarter n a l (lab c i b) = lab c (σ i) b := by
  by_cases hex : ∃ k : Fin 4, level c k = l
  · obtain ⟨k, rfl⟩ := hex
    fin_cases a <;> fin_cases k
    · refine ⟨gen0, ?_⟩
      intro i b
      simpa [physicalAtom, faceMove, sliceMove, movePermutation, finiteAtom, face, slice, level, lo, hi] using
        (physical_atom_lab hc (Sum.inl (0 : Fin 6)) i b)
    · refine ⟨gen6, ?_⟩
      intro i b
      simpa [physicalAtom, faceMove, sliceMove, movePermutation, finiteAtom, face, slice, level, lo, hi] using
        (physical_atom_lab hc (Sum.inr (0 : Fin 6)) i b)
    · refine ⟨gen7, ?_⟩
      intro i b
      simpa [physicalAtom, faceMove, sliceMove, movePermutation, finiteAtom, face, slice, level, lo, hi] using
        (physical_atom_lab hc (Sum.inr (1 : Fin 6)) i b)
    · refine ⟨gen1, ?_⟩
      intro i b
      simpa [physicalAtom, faceMove, sliceMove, movePermutation, finiteAtom, face, slice, level, lo, hi] using
        (physical_atom_lab hc (Sum.inl (1 : Fin 6)) i b)
    · refine ⟨gen2, ?_⟩
      intro i b
      simpa [physicalAtom, faceMove, sliceMove, movePermutation, finiteAtom, face, slice, level, lo, hi] using
        (physical_atom_lab hc (Sum.inl (2 : Fin 6)) i b)
    · refine ⟨gen8, ?_⟩
      intro i b
      simpa [physicalAtom, faceMove, sliceMove, movePermutation, finiteAtom, face, slice, level, lo, hi] using
        (physical_atom_lab hc (Sum.inr (2 : Fin 6)) i b)
    · refine ⟨gen9, ?_⟩
      intro i b
      simpa [physicalAtom, faceMove, sliceMove, movePermutation, finiteAtom, face, slice, level, lo, hi] using
        (physical_atom_lab hc (Sum.inr (3 : Fin 6)) i b)
    · refine ⟨gen3, ?_⟩
      intro i b
      simpa [physicalAtom, faceMove, sliceMove, movePermutation, finiteAtom, face, slice, level, lo, hi] using
        (physical_atom_lab hc (Sum.inl (3 : Fin 6)) i b)
    · refine ⟨gen4, ?_⟩
      intro i b
      simpa [physicalAtom, faceMove, sliceMove, movePermutation, finiteAtom, face, slice, level, lo, hi] using
        (physical_atom_lab hc (Sum.inl (4 : Fin 6)) i b)
    · refine ⟨gen10, ?_⟩
      intro i b
      simpa [physicalAtom, faceMove, sliceMove, movePermutation, finiteAtom, face, slice, level, lo, hi] using
        (physical_atom_lab hc (Sum.inr (4 : Fin 6)) i b)
    · refine ⟨gen11, ?_⟩
      intro i b
      simpa [physicalAtom, faceMove, sliceMove, movePermutation, finiteAtom, face, slice, level, lo, hi] using
        (physical_atom_lab hc (Sum.inr (5 : Fin 6)) i b)
    · refine ⟨gen5, ?_⟩
      intro i b
      simpa [physicalAtom, faceMove, sliceMove, movePermutation, finiteAtom, face, slice, level, lo, hi] using
        (physical_atom_lab hc (Sum.inl (5 : Fin 6)) i b)
  · refine ⟨1, ?_⟩
    intro i b
    have hcoord : coordinate (lab c i b).val.1 a ≠ l := by
      intro h
      apply hex
      refine ⟨coordinate (pos (1 : Fin 4) i) a, ?_⟩
      calc
        level c (coordinate (pos (1 : Fin 4) i) a) =
            coordinate (embed c (lab (1 : Fin 4) i b)).val.1 a := by fin_cases a <;> rfl
        _ = coordinate (lab c i b).val.1 a :=
          congrArg (fun s : Sticker n => coordinate s.val.1 a) (embed_lab c i b)
        _ = l := h
    simp [sliceQuarter, hcoord]

private theorem RubikWing.arbitrary_word_action {n : ℕ} {c : Fin n} (hc : Admissible n c)
    (w : List (Move n)) : ∃ σ : Equiv.Perm Label,
    ∀ i b, RubikBand.wordPerm w (lab c i b) = lab c (σ i) b := by
  have hmove (m : Move n) : ∃ σ : Equiv.Perm Label,
      ∀ i b, movePermutation m (lab c i b) = lab c (σ i) b := by
    obtain ⟨σ,hσ⟩ := arbitrary_quarter_action hc m.1 m.2.1
    have hp (k : ℕ) : ∀ i b,
        (sliceQuarter n m.1 m.2.1 ^ k) (lab c i b) = lab c ((σ ^ k) i) b := by
      induction k with
      | zero => intro i b; simp
      | succ k ih =>
        intro i b
        simp only [pow_succ, Equiv.Perm.mul_apply, hσ, ih]
    exact ⟨σ ^ (m.2.2.val + 1), hp _⟩
  induction w with
  | nil => exact ⟨1, by intro i b; rfl⟩
  | cons m w ih =>
    obtain ⟨σ,hσ⟩ := hmove m
    obtain ⟨τ,hτ⟩ := ih
    refine ⟨τ * σ, ?_⟩
    intro i b
    simp only [RubikBand.wordPerm, List.map_cons, List.reverse_cons,
      List.prod_append, List.prod_singleton, Equiv.Perm.mul_apply]
    change RubikBand.wordPerm w (movePermutation m (lab c i b)) = _
    rw [hσ, hτ]

theorem proof_RubikWing_reachable_cleanup {n : ℕ} {c : Fin n} (hc : Admissible n c)
    (r : Position n) : ∃ w : List (Move n), w.length ≤ uniformCost ∧
    RubikBand.StrictControl c w ∧
    (∀ i b, applyWord w r.val (lab c i b) = solved n (lab c i b)) ∧
    (∀ s : Sticker n, ¬ RubikBand.Band c s → RubikBand.wordPerm w s = s) := by
  have hcol (w : List (Move n)) (C : Colouring n) (s : Sticker n) :
      applyWord w C s = C ((RubikBand.wordPerm w)⁻¹ s) := by
    induction w generalizing C with
    | nil => rfl
    | cons m w ih =>
      change applyWord w (applyMove m C) s = _
      rw [ih]
      simp [applyMove, RubikBand.wordPerm, List.reverse_cons,
        List.prod_append, Equiv.Perm.mul_apply]
  obtain ⟨v,hv⟩ := r.property
  obtain ⟨σ,hσ⟩ := arbitrary_word_action hc v
  have hclean := uniform_cleanup hc σ⁻¹
  refine ⟨solverWord c σ⁻¹, hclean.1, hclean.2.1, ?_, hclean.2.2.2⟩
  intro i b
  have hD : (RubikBand.wordPerm (solverWord c σ⁻¹))⁻¹ (lab c i b) = lab c (σ i) b := by
    apply Equiv.Perm.inv_eq_iff_eq.mpr
    symm
    simpa using hclean.2.2.1 (σ i) b
  have hV : (RubikBand.wordPerm v)⁻¹ (lab c (σ i) b) = lab c i b := by
    apply Equiv.Perm.inv_eq_iff_eq.mpr
    exact (hσ i b).symm
  rw [hcol, hD, ← hv, hcol, hV]
