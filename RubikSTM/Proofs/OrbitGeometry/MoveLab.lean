import RubikSTM.Definitions.OrbitGeometry.GenPerm
set_option autoImplicit false
open Rubik RubikGeometry
set_option maxHeartbeats 2000000
theorem proof_RubikGeometry_move_lab {n : ℕ} {a b : Fin n} (hg : Generic n a b) (k : Fin 8) (i : Fin 24) :
    movePermutation (genMove a b k) (lab a b i) = lab a b (genPerm k i) := by
  have revlo : (lo a).rev = hi a := by
    apply Fin.ext
    simp [lo, hi, Fin.rev] <;> omega
  have revhi : (hi a).rev = lo a := by
    apply Fin.ext
    simp [lo, hi, Fin.rev] <;> omega
  have ha := hg.one_le_a
  have hb := hg.one_le_b
  have has := hg.a_small
  have hbs := hg.b_small
  have han := a.isLt
  have hbn := b.isLt
  have hab : a.val ≠ b.val := by intro h; exact hg.ne (Fin.ext h)
  have d01 : lo a ≠ a := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d02 : lo a ≠ b := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d03 : lo a ≠ a.rev := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d04 : lo a ≠ b.rev := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d05 : lo a ≠ hi a := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d12 : a ≠ b := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d13 : a ≠ a.rev := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d14 : a ≠ b.rev := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d15 : a ≠ hi a := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d23 : b ≠ a.rev := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d24 : b ≠ b.rev := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d25 : b ≠ hi a := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d34 : a.rev ≠ b.rev := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d35 : a.rev ≠ hi a := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  have d45 : b.rev ≠ hi a := by
    intro he
    have he' := congrArg Fin.val he
    try simp only [lo, hi, Fin.rev, Fin.val_mk] at he'
    omega
  fin_cases k <;> fin_cases i <;> apply Subtype.ext <;>
    simp [movePermutation, genMove, genPerm, gen0, gen1, gen2, gen3, gen4, gen5, gen6, gen7,
      lab, rawLab, posTable, normalTable, sliceQuarter, surfaceRotation, rawRotation,
      coordinateRotation, normalRotation, normalForward, coordinate, revlo, revhi, d01, Ne.symm d01, d02, Ne.symm d02, d03, Ne.symm d03, d04, Ne.symm d04, d05, Ne.symm d05, d12, Ne.symm d12, d13, Ne.symm d13, d14, Ne.symm d14, d15, Ne.symm d15, d23, Ne.symm d23, d24, Ne.symm d24, d25, Ne.symm d25, d34, Ne.symm d34, d35, Ne.symm d35, d45, Ne.symm d45]

#print axioms proof_RubikGeometry_move_lab
