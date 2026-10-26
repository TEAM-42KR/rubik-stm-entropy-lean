import RubikSTM.Proofs.Construction.Control.Physical.UniformSignedModel
import RubikSTM.Definitions.Construction.Control.Physical.ActualMoves
set_option autoImplicit false

theorem RubikConstruction.Control.Physical.uniform_signed_model :
    ∃ L : ℕ, ∀ σ : Equiv.Perm (Fin 24), ∃ letters : List RubikConstruction.Control.Physical.SignedLetter, letters.length ≤ L ∧ RubikConstruction.Control.finiteEval (FreeGroup.mk letters) = σ ∧ RubikConstruction.Control.deletion (FreeGroup.mk letters) = 1 :=
  @proof_RubikConstruction_Control_Physical_uniform_signed_model
