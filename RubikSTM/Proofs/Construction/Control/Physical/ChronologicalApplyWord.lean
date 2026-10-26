import Mathlib
import RubikSTM.Definitions.Construction.Control.Physical.ActualMoves
import RubikSTM.Definitions.OrbitGeometry.GenPerm
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open Rubik RubikConstruction.Control RubikConstruction.Control.Physical
theorem proof_RubikConstruction_Control_Physical_chronological_applyWord {n : ℕ} (ms : List (Move n)) (c : Colouring n) :
    applyWord ms c = fun s => c ((chronological ms)⁻¹ s) := by
  induction ms generalizing c with
  | nil => rfl
  | cons m ms ih =>
    change applyWord ms (applyMove m c) = _
    rw [ih]
    funext s
    simp [chronological, applyMove]
