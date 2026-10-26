import RubikSTM.Proofs.OBTM.Band.UniformKernelWords
import RubikSTM.Definitions.OBTM.Band.Finite.ModelEval
set_option autoImplicit false

theorem RubikOBTM.Band.uniform_kernel_words :
    ∃ D : ℕ, ∀ (n : ℕ) (a u v : Fin n), RubikOBTM.Band.Admissible n a u v → ∀ t : RubikOBTM.Band.Finite.Alphabet, ∃ w : List (RubikOBTM.BlockMove n), w.length ≤ D ∧ RubikOBTM.Band.CleanAction a u v (RubikOBTM.Band.Finite.kernel t) (RubikOBTM.Band.wordPerm w) :=
  @proof_RubikOBTM_Band_uniform_kernel_words
