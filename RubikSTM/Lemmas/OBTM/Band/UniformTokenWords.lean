import RubikSTM.Proofs.OBTM.Band.UniformTokenWords
import RubikSTM.Definitions.OBTM.Band.Finite.ModelEval
set_option autoImplicit false

theorem RubikOBTM.Band.uniform_token_words :
    ∃ D : ℕ, ∀ (n : ℕ) (a u v : Fin n), RubikOBTM.Band.Admissible n a u v → ∀ ts : List RubikOBTM.Band.Finite.Token, ∃ w : List (RubikOBTM.BlockMove n), w.length ≤ D*ts.length ∧ RubikOBTM.Band.CleanAction a u v (RubikOBTM.Band.Finite.signedEval ts) (RubikOBTM.Band.wordPerm w) :=
  @proof_RubikOBTM_Band_uniform_token_words
