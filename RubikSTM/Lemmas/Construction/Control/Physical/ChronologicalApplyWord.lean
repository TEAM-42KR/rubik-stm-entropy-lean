import RubikSTM.Proofs.Construction.Control.Physical.ChronologicalApplyWord
import RubikSTM.Definitions.Construction.Control.Physical.ActualMoves
set_option autoImplicit false

theorem RubikConstruction.Control.Physical.chronological_applyWord :
    ∀ {n : ℕ} (ms : List (Rubik.Move n)) (c : Rubik.Colouring n), Rubik.applyWord ms c = fun s => c ((RubikConstruction.Control.Physical.chronological ms)⁻¹ s) :=
  @proof_RubikConstruction_Control_Physical_chronological_applyWord
