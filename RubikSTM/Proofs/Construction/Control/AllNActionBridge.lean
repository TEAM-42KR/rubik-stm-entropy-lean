import Mathlib
import RubikSTM.Definitions.Construction.Control.Physical.ActualMoves
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Lemmas.OrbitGeometry.MoveLab
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open Rubik RubikConstruction.Control RubikConstruction.Control.Physical
theorem proof_RubikConstruction_Control_all_n_action_bridge : AllNActionBridge := by
  intro n a b ha hb has hbs hab
  have hg : RubikGeometry.Generic n a b := ⟨ha, hb, has, hbs, hab⟩
  have revlo : (low a).rev = high a := by
    apply Fin.ext
    simp [low, high, Fin.rev] <;> omega
  have revhi : (high a).rev = low a := by
    apply Fin.ext
    simp [low, high, Fin.rev] <;> omega
  have ha := hg.one_le_a
  have hb := hg.one_le_b
  have has := hg.a_small
  have hbs := hg.b_small
  have han := a.isLt
  have hbn := b.isLt
  have hab : a.val ≠ b.val := by intro h; exact hg.ne (Fin.ext h)
  have d01 : low a ≠ a := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at he'
    omega
  have d02 : low a ≠ b := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at he'
    omega
  have d03 : low a ≠ a.rev := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at he'
    omega
  have d04 : low a ≠ b.rev := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at he'
    omega
  have d05 : low a ≠ high a := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at he'
    omega
  have d12 : a ≠ b := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at he'
    omega
  have d13 : a ≠ a.rev := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at he'
    omega
  have d14 : a ≠ b.rev := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at he'
    omega
  have d15 : a ≠ high a := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at he'
    omega
  have d23 : b ≠ a.rev := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at he'
    omega
  have d24 : b ≠ b.rev := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at he'
    omega
  have d25 : b ≠ high a := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at he'
    omega
  have d34 : a.rev ≠ b.rev := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at he'
    omega
  have d35 : a.rev ≠ high a := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at he'
    omega
  have d45 : b.rev ≠ high a := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [low, high, Fin.rev, Fin.val_mk] at he'
    omega
  intro t i
  cases t with
  | inl f =>
    fin_cases f
    · exact RubikGeometry.move_lab hg 0 i
    · exact RubikGeometry.move_lab hg 1 i
    · exact RubikGeometry.move_lab hg 2 i
    · exact RubikGeometry.move_lab hg 3 i
    · exact RubikGeometry.move_lab hg 4 i
    · exact RubikGeometry.move_lab hg 5 i
  | inr ax =>
    fin_cases ax
    · exact RubikGeometry.move_lab hg 6 i
    all_goals fin_cases i <;> apply Subtype.ext <;>
      simp [physicalAtom, sliceMove, finiteAtom, slice, slice1, slice2,
        movePermutation, lab, rawLab, posTable, normalTable,
        sliceQuarter, surfaceRotation, rawRotation, coordinateRotation,
        normalRotation, normalForward, coordinate, revlo, revhi,
        d01, Ne.symm d01, d02, Ne.symm d02, d03, Ne.symm d03,
        d04, Ne.symm d04, d05, Ne.symm d05, d12, Ne.symm d12,
        d13, Ne.symm d13, d14, Ne.symm d14, d15, Ne.symm d15,
        d23, Ne.symm d23, d24, Ne.symm d24, d25, Ne.symm d25,
        d34, Ne.symm d34, d35, Ne.symm d35, d45, Ne.symm d45]
