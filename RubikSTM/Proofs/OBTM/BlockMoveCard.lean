import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem proof_RubikOBTM_blockMove_card (n : ℕ) : Fintype.card (RubikOBTM.BlockMove n) = 18 * (n - 1) := by
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  omega
