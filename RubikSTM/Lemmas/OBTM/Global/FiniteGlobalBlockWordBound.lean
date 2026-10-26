import RubikSTM.Proofs.OBTM.Global.FiniteGlobalBlockWordBound
import RubikSTM.Definitions.OBTM.Global.RectangleCompiler
set_option autoImplicit false

theorem RubikOBTM.Global.finite_global_block_word_bound :
    ∃ C : ℕ, ∀ (n : ℕ), 2 ≤ n → ∀ (h : ℕ) (f : RubikGlobal.I n → Fin h) (cost : RubikGlobalWord.GroupPair h → ℕ), (∀ (p : RubikGlobalWord.GroupPair h) (c d : Rubik.Position n), ∃ w : List (RubikOBTM.BlockMove n), w.length ≤ cost p ∧ RubikOBTM.Global.Recolour (RubikGlobalWord.Region f (Sum.inl p)) c.val d.val w) → ∀ c d : Rubik.Position n, ∃ w : List (RubikOBTM.BlockMove n), w.length ≤ (∑ p, cost p) + C * (RubikGlobalWord.sameCount f + 6 * Fintype.card (RubikGlobal.I n)) + 4 * RubikCore.cleanupBound ∧ RubikOBTM.applyBlockWord w c.val = d.val :=
  @proof_RubikOBTM_Global_finite_global_block_word_bound
