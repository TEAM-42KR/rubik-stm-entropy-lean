import RubikSTM.Proofs.LocalActions.Generic.ChronologicalAppend
import RubikSTM.Definitions.LocalActions.Generic.ModelEval
set_option autoImplicit false
open RubikConstruction.Control.Physical

theorem RubikLocal.Generic.chronological_append :
    ∀ {n : ℕ} (u v : List (Rubik.Move n)), RubikConstruction.Control.Physical.chronological (u ++ v) = RubikConstruction.Control.Physical.chronological v * RubikConstruction.Control.Physical.chronological u :=
  @proof_RubikLocal_Generic_chronological_append
