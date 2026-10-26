import RubikSTM.Definitions.Core.CoreAction
import RubikSTM.Lemmas.Core.CoreCardLe
set_option autoImplicit false

open Rubik RubikCore
open scoped Classical

theorem proof_RubikCore_coreColouring_card_le (n : ℕ) : Fintype.card (CoreColouring n) ≤ cleanupBound := by
  classical
  change Fintype.card (CoreSticker n → Colour) ≤ 6 ^ 162
  rw [Fintype.card_fun]
  have hc : Fintype.card Colour = 6 := by
    simp only [Colour, Rubik.Normal, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  rw [hc]
  exact Nat.pow_le_pow_right (by decide) (RubikCore.core_card_le n)

#print axioms proof_RubikCore_coreColouring_card_le
