import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Lemmas.OBTM.ParallelSlicesApply
import RubikSTM.Lemmas.OBTM.BlockPowerApply
import RubikSTM.Lemmas.OBTM.SurfaceRotationFour
set_option autoImplicit false

theorem proof_RubikOBTM_slice_two_blocks {n : ℕ} (hn : 2 ≤ n) (m : Rubik.Move n) :
    ∃ w : List (RubikOBTM.BlockMove n), w.length ≤ 2 ∧
      ((w.map RubikOBTM.blockPermutation).reverse.prod) = Rubik.movePermutation m := by
  rcases m with ⟨a, l, q⟩
  have hf (t : Rubik.Sticker n) :
      Rubik.coordinate (Rubik.surfaceRotation n a t).val.1 a =
        Rubik.coordinate t.val.1 a := by
    fin_cases a <;>
      simp [Rubik.surfaceRotation, Rubik.rawRotation, Rubik.coordinateRotation, Rubik.coordinate]
  have hp (r : ℕ) (t : Rubik.Sticker n) :
      Rubik.coordinate ((Rubik.surfaceRotation n a ^ r) t).val.1 a =
        Rubik.coordinate t.val.1 a := by
    induction r with
    | zero => simp
    | succ r ih => simp only [pow_succ', Equiv.Perm.mul_apply, hf, ih]
  have hs (t : Rubik.Sticker n) : Rubik.movePermutation (a, l, q) t =
      if Rubik.coordinate t.val.1 a = l
      then (Rubik.surfaceRotation n a ^ (q.val + 1)) t else t := by
    simpa [Rubik.movePermutation] using
      RubikOBTM.parallel_slices_apply a [l] (by simp) (q.val + 1) t
  by_cases hzero : l.val = 0
  · let b : RubikOBTM.BlockMove n := (a, false, ⟨0, by omega⟩, q)
    refine ⟨[b], by simp, ?_⟩
    apply Equiv.ext
    intro s
    simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.prod_cons, List.prod_nil, mul_one]
    rw [hs]
    change (RubikOBTM.blockQuarter n a false ⟨0, by omega⟩ ^ (q.val + 1)) s = _
    rw [RubikOBTM.block_power_apply]
    have he : RubikOBTM.selected a false ⟨0, by omega⟩ (Rubik.coordinate s.val.1 a) ↔
        Rubik.coordinate s.val.1 a = l := by
      simp only [RubikOBTM.selected, Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro h; apply Fin.ext; omega
      · intro h; rw [h]; omega
    simp only [he]
  · by_cases hlast : l.val = n - 1
    · let b : RubikOBTM.BlockMove n := (a, true, ⟨0, by omega⟩, q)
      refine ⟨[b], by simp, ?_⟩
      apply Equiv.ext
      intro s
      simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.prod_cons, List.prod_nil, mul_one]
      rw [hs]
      change (RubikOBTM.blockQuarter n a true ⟨0, by omega⟩ ^ (q.val + 1)) s = _
      rw [RubikOBTM.block_power_apply]
      have he : RubikOBTM.selected a true ⟨0, by omega⟩ (Rubik.coordinate s.val.1 a) ↔
          Rubik.coordinate s.val.1 a = l := by
        simp only [RubikOBTM.selected, Bool.false_eq_true, ↓reduceIte, Fin.val_mk]
        constructor
        · intro h; apply Fin.ext; have := (Rubik.coordinate s.val.1 a).isLt; omega
        · intro h; rw [h]; omega
      simp only [he]
    · let b : RubikOBTM.BlockMove n := (a, false, ⟨l.val, by omega⟩, q)
      let iq : Fin 3 := ⟨2 - q.val, by omega⟩
      let c : RubikOBTM.BlockMove n := (a, false, ⟨l.val - 1, by omega⟩, iq)
      refine ⟨[b, c], by simp, ?_⟩
      apply Equiv.ext
      intro s
      simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.prod_append, List.prod_cons, List.prod_nil, mul_one,
        Equiv.Perm.mul_apply]
      rw [hs]
      change (RubikOBTM.blockQuarter n a false ⟨l.val - 1, by omega⟩ ^ (iq.val + 1))
        ((RubikOBTM.blockQuarter n a false ⟨l.val, by omega⟩ ^ (q.val + 1)) s) = _
      rw [RubikOBTM.block_power_apply a false ⟨l.val, by omega⟩ (q.val + 1) s]
      by_cases hlow : (Rubik.coordinate s.val.1 a).val < l.val
      · have hupper : RubikOBTM.selected a false ⟨l.val, by omega⟩ (Rubik.coordinate s.val.1 a) := by
          simp only [RubikOBTM.selected, Bool.false_eq_true, ↓reduceIte, Fin.val_mk]; omega
        have he : Rubik.coordinate s.val.1 a ≠ l := by intro he; rw [he] at hlow; omega
        simp only [if_pos hupper, if_neg he]
        rw [RubikOBTM.block_power_apply]
        have hlower : RubikOBTM.selected a false ⟨l.val - 1, by omega⟩
            (Rubik.coordinate ((Rubik.surfaceRotation n a ^ (q.val + 1)) s).val.1 a) := by
          rw [hp]; simp only [RubikOBTM.selected, Bool.false_eq_true, ↓reduceIte, Fin.val_mk]; omega
        rw [if_pos hlower, ← Equiv.Perm.mul_apply, ← pow_add]
        have hiq : iq.val + 1 + (q.val + 1) = 4 := by dsimp [iq]; omega
        rw [hiq, RubikOBTM.surfaceRotation_four]
        rfl
      · by_cases he : Rubik.coordinate s.val.1 a = l
        · have hupper : RubikOBTM.selected a false ⟨l.val, by omega⟩ (Rubik.coordinate s.val.1 a) := by
            simp only [RubikOBTM.selected, Bool.false_eq_true, ↓reduceIte, Fin.val_mk]; rw [he]; omega
          simp only [if_pos hupper, if_pos he]
          rw [RubikOBTM.block_power_apply]
          have hlower : ¬RubikOBTM.selected a false ⟨l.val - 1, by omega⟩
              (Rubik.coordinate ((Rubik.surfaceRotation n a ^ (q.val + 1)) s).val.1 a) := by
            rw [hp, he]; simp only [RubikOBTM.selected, Bool.false_eq_true, ↓reduceIte, Fin.val_mk]; omega
          rw [if_neg hlower]
        · have hupper : ¬RubikOBTM.selected a false ⟨l.val, by omega⟩ (Rubik.coordinate s.val.1 a) := by
            simp only [RubikOBTM.selected, Bool.false_eq_true, ↓reduceIte, Fin.val_mk]
            have hne : (Rubik.coordinate s.val.1 a).val ≠ l.val := fun h => he (Fin.ext h)
            omega
          simp only [if_neg hupper, if_neg he]
          rw [RubikOBTM.block_power_apply]
          have hlower : ¬RubikOBTM.selected a false ⟨l.val - 1, by omega⟩ (Rubik.coordinate s.val.1 a) := by
            simp only [RubikOBTM.selected, Bool.false_eq_true, ↓reduceIte, Fin.val_mk]; omega
          rw [if_neg hlower]
