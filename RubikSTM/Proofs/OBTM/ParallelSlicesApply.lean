import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem proof_RubikOBTM_parallel_slices_apply {n : ℕ} (a : Rubik.Axis) (ls : List (Fin n)) (hl : ls.Nodup)
    (j : ℕ) (s : Rubik.Sticker n) :
    ((ls.map (fun l => Rubik.sliceQuarter n a l ^ j)).reverse.prod) s =
      if Rubik.coordinate s.val.1 a ∈ ls then (Rubik.surfaceRotation n a ^ j) s else s := by
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
  have hs (l : Fin n) (r : ℕ) (t : Rubik.Sticker n) :
      (Rubik.sliceQuarter n a l ^ r) t =
        if Rubik.coordinate t.val.1 a = l then (Rubik.surfaceRotation n a ^ r) t else t := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih]
      by_cases h : Rubik.coordinate t.val.1 a = l
      · simp [h, Rubik.sliceQuarter, hp, pow_succ', Equiv.Perm.mul_apply]
      · simp [h, Rubik.sliceQuarter]
  induction ls generalizing s with
  | nil => simp
  | cons l ls ih =>
    obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hl
    simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_cons,
      List.prod_nil, mul_one, Equiv.Perm.mul_apply]
    rw [hs]
    by_cases h : Rubik.coordinate s.val.1 a = l
    · simp only [if_pos h]
      rw [ih hnodup]
      simp [hp, h, hnot]
    · simp only [if_neg h]
      rw [ih hnodup]
      simp [h]
