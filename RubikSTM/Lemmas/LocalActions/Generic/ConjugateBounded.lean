import RubikSTM.Proofs.LocalActions.Generic.ConjugateBounded
import RubikSTM.Definitions.LocalActions.Generic.ModelEval
set_option autoImplicit false
open RubikLocal.Generic RubikConstruction.Control.Physical

theorem RubikLocal.Generic.conjugate_bounded :
    ∀ (L : ℕ) (cw : RubikLocal.Generic.Perm → RubikLocal.Generic.ControlLetters) (hcw : ∀ q, (cw q).length ≤ L ∧ RubikConstruction.Control.finiteEval (FreeGroup.mk (cw q)) = q) {n : ℕ} (a b : Fin n) (hg : RubikGeometry.Generic n a b) (t : RubikLocal.Generic.Token), (RubikLocal.Generic.conjugateMoves a b cw t).length ≤ 2 * L + 8 ∧ RubikLocal.Generic.LocalAction a b (RubikLocal.Generic.tokenPerm t) (RubikConstruction.Control.Physical.chronological (RubikLocal.Generic.conjugateMoves a b cw t)) :=
  @proof_RubikLocal_Generic_conjugate_bounded
