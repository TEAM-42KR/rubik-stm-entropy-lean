import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem proof_RubikOBTM_block_power_apply {n : ℕ} (a : Rubik.Axis) (side : Bool) (k : Fin (n - 1))
    (j : ℕ) (s : Rubik.Sticker n) :
    (RubikOBTM.blockQuarter n a side k ^ j) s =
      if RubikOBTM.selected a side k (Rubik.coordinate s.val.1 a)
      then (Rubik.surfaceRotation n a ^ j) s else s := by
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
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih]
    by_cases h : RubikOBTM.selected a side k (Rubik.coordinate s.val.1 a)
    · simp [h, RubikOBTM.blockQuarter, hp, pow_succ', Equiv.Perm.mul_apply]
    · simp [h, RubikOBTM.blockQuarter]
