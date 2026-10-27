import RubikSTM.Definitions.Geometry.StmGraph
set_option autoImplicit false

theorem proof_Rubik_move_card (n : ℕ) : Fintype.card (Rubik.Move n) = 9 * n := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  omega
