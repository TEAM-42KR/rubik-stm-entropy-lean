import RubikSTM.Proofs.GlobalWords.GenericLocalRecolour
import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
set_option autoImplicit false

theorem RubikGlobalWord.generic_local_recolour :
    ∃ C : ℕ, ∀ (n : ℕ) (p : RubikGlobal.Q n) (c d : Rubik.Position n),
  ∃ w : List (Rubik.Move n), w.length ≤ C ∧
    RubikGlobalWord.Recolour (RubikGlobal.GenericRange p) c.val d.val w :=
  @proof_RubikGlobalWord_generic_local_recolour
