import RubikSTM.Proofs.OBTM.Band.UniformCleanEvenControl
import RubikSTM.Definitions.OBTM.Band.CleanAction
set_option autoImplicit false

theorem RubikOBTM.Band.uniform_clean_even_control :
    ∃ C : ℕ, 0 < C ∧ ∀ (n : ℕ) (a u v : Fin n), RubikOBTM.Band.Admissible n a u v → ∀ p q : Equiv.Perm (Fin 24), p ∈ alternatingGroup (Fin 24) → q ∈ alternatingGroup (Fin 24) → ∃ w : List (RubikOBTM.BlockMove n), w.length ≤ C ∧ RubikOBTM.Band.CleanAction a u v (p,q) (RubikOBTM.Band.wordPerm w) :=
  @proof_RubikOBTM_Band_uniform_clean_even_control
