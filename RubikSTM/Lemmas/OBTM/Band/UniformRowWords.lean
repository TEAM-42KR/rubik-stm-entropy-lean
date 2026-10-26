import RubikSTM.Proofs.OBTM.Band.UniformRowWords
import RubikSTM.Definitions.OBTM.Band.CleanAction
set_option autoImplicit false

theorem RubikOBTM.Band.uniform_row_words :
    ∃ L : ℕ, ∀ (n : ℕ) (a : Fin n), 1 ≤ a.val → 2*a.val+2 ≤ n → ∀ σ : Equiv.Perm (Fin 24), ∃ ms : List (Rubik.Move n), ms.length ≤ L ∧ RubikBand.StrictControl a ms ∧ ∀ (d : Fin n), 1 ≤ d.val → 2*d.val+2 ≤ n → a ≠ d → ∀ i : Fin 24, (RubikBand.wordPerm ms (RubikOBTM.Band.plus a d i) = RubikOBTM.Band.plus a d (σ i)) ∧ (RubikBand.wordPerm ms (RubikOBTM.Band.minus a d i) = RubikOBTM.Band.minus a d (σ i)) :=
  @proof_RubikOBTM_Band_uniform_row_words
