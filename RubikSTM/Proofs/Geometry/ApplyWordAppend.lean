import RubikSTM.Definitions.Geometry.StmGraph
set_option autoImplicit false

theorem proof_Rubik_applyWord_append {n : ℕ} (u v : List (Rubik.Move n)) (c : Rubik.Colouring n) : Rubik.applyWord (u ++ v) c = Rubik.applyWord v (Rubik.applyWord u c) := by
  simp [Rubik.applyWord, List.foldl_append]
