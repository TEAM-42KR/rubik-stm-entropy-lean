import RubikSTM.Definitions.Core.Project
set_option autoImplicit false

open RubikCore

theorem proof_RubikCore_levelCode_inj {n : ℕ} {x y : Fin n} (hx : IsLevel x) (hy : IsLevel y)
    (h : levelCode x = levelCode y) : x = y := by
  classical
  unfold levelCode at h
  apply Fin.ext
  split_ifs at h with hx0 hy0 hy1 hx1 hy1 <;>
    simp_all [IsLevel, Fin.ext_iff, Fin.rev] <;> omega

#print axioms proof_RubikCore_levelCode_inj
