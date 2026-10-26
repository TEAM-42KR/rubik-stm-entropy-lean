import RubikSTM.Proofs.LocalActions.Generic.RealizeTokensCorrect
import RubikSTM.Definitions.LocalActions.Generic.ModelEval
set_option autoImplicit false
open RubikLocal.Generic RubikConstruction.Control.Physical

theorem RubikLocal.Generic.realize_tokens_correct :
    ∀ (L : ℕ) (cw : RubikLocal.Generic.Perm → RubikLocal.Generic.ControlLetters) (hcw : ∀ q, (cw q).length ≤ L ∧ RubikConstruction.Control.finiteEval (FreeGroup.mk (cw q)) = q) {n : ℕ} (a b : Fin n) (hg : RubikGeometry.Generic n a b) (ts : List RubikLocal.Generic.Token), (RubikLocal.Generic.realizeTokens a b cw ts).length ≤ ts.length * (2 * L + 8) ∧ RubikLocal.Generic.LocalAction a b (RubikLocal.Generic.evalTokens ts) (RubikConstruction.Control.Physical.chronological (RubikLocal.Generic.realizeTokens a b cw ts)) :=
  @proof_RubikLocal_Generic_realize_tokens_correct
