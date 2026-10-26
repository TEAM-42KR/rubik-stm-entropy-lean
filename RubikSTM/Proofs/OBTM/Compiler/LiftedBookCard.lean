import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.VectorAction
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_lifted_book_card {T k L : ℕ} (hT : 0 < T) (K : Fin T → Type*)
  [∀ p, Group (K p)] (C : ∀ p, Finset (K p)) (B : RubikOBTM.Periodic.Book hT K C k L)
  (i : Fin L) : (RubikOBTMCompiler.liftedBook hT K C B i).card ≤ (B i).card := by
  classical
  exact Finset.card_image_le

#print axioms proof_RubikOBTMCompiler_lifted_book_card
