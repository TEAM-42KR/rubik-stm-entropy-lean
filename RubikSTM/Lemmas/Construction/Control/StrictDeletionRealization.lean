import RubikSTM.Proofs.Construction.Control.StrictDeletionRealization
import Mathlib
import RubikSTM.Definitions.Construction.Control.K
set_option autoImplicit false

theorem RubikConstruction.Control.strict_deletion_realization :
    ∀ (σ : Equiv.Perm (Fin 24)), ∃ w : RubikConstruction.Control.Word, RubikConstruction.Control.finiteEval w = σ ∧ RubikConstruction.Control.deletion w = 1 :=
  @proof_RubikConstruction_Control_strict_deletion_realization
