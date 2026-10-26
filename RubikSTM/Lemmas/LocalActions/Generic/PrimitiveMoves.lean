import RubikSTM.Proofs.LocalActions.Generic.PrimitiveMoves
import RubikSTM.Definitions.LocalActions.Generic.ModelEval
set_option autoImplicit false
open RubikLocal.Generic RubikConstruction.Control.Physical

theorem RubikLocal.Generic.primitive_moves :
    ∀ {n : ℕ} (a b : Fin n) (hg : RubikGeometry.Generic n a b) (s : Bool), (RubikLocal.Generic.primitiveMoves a b s).length = 8 ∧ RubikLocal.Generic.LocalAction a b (if s then RubikGeometry.t0 else RubikGeometry.t0⁻¹) (RubikConstruction.Control.Physical.chronological (RubikLocal.Generic.primitiveMoves a b s)) :=
  @proof_RubikLocal_Generic_primitive_moves
