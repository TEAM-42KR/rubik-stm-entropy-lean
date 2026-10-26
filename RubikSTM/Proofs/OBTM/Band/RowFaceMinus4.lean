import RubikSTM.Definitions.OBTM.Band.SlabWord
set_option autoImplicit false
open Rubik RubikConstruction.Control RubikOBTM.Band
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

theorem proof_RubikOBTM_Band_row_face_minus_4 {n : ℕ} (a d : Fin n)
    (ha : 1 ≤ a.val) (hd : 1 ≤ d.val) (has : 2*a.val+2 ≤ n)
    (hds : 2*d.val+2 ≤ n) (had : a ≠ d) (j : Fin 24) :
    physicalAtom a (Sum.inl (4 : Fin 6)) (minus a d j) = minus a d (finiteAtom (Sum.inl (4 : Fin 6)) j) := by
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
  have rl : (low a).rev = high a := by apply Fin.ext; simp [low,high,Fin.rev]
  have rh : (high a).rev = low a := by apply Fin.ext; simp [low,high,Fin.rev]; omega
  fin_cases j <;> apply Subtype.ext <;>
    simp [minus,physicalAtom,faceMove,finiteAtom,face,face0,face1,face2,face3,face4,face5,
      movePermutation,lab,rawLab,posTable,normalTable,sliceQuarter,surfaceRotation,
      rawRotation,coordinateRotation,normalRotation,normalForward,coordinate,rl,rh,
      d01, Ne.symm d01, d02, Ne.symm d02, d03, Ne.symm d03, d04, Ne.symm d04, d05, Ne.symm d05, d12, Ne.symm d12, d13, Ne.symm d13, d14, Ne.symm d14, d15, Ne.symm d15, d23, Ne.symm d23, d24, Ne.symm d24, d25, Ne.symm d25, d34, Ne.symm d34, d35, Ne.symm d35, d45, Ne.symm d45]
