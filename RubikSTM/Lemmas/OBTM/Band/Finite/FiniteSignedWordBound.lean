import RubikSTM.Proofs.OBTM.Band.Finite.FiniteSignedWordBound
import RubikSTM.Definitions.OBTM.Band.Finite.ModelEval
set_option autoImplicit false

theorem RubikOBTM.Band.Finite.finite_signed_word_bound :
    ∃ M : ℕ, 0 < M ∧ ∀ p q : RubikOBTM.Band.Perm,
    p ∈ alternatingGroup RubikOBTM.Band.Label → q ∈ alternatingGroup RubikOBTM.Band.Label →
    ∃ w : List RubikOBTM.Band.Finite.Token,
      w.length ≤ M ∧ RubikOBTM.Band.Finite.signedEval w = (p,q) :=
  @proof_RubikOBTM_Band_Finite_finite_signed_word_bound
