import Mathlib
import RubikSTM.Definitions.Construction.Control.Physical.ActualMoves
import RubikSTM.Definitions.OrbitGeometry.GenPerm
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open Rubik RubikConstruction.Control RubikConstruction.Control.Physical
theorem proof_RubikConstruction_Control_Physical_actual_moves_allowed {n : ℕ} (a : Fin n) (letters : List SignedLetter) :
    ∀ m ∈ actualMoves a letters, Allowed a m := by
  intro m hm
  obtain ⟨⟨t, s⟩, _, rfl⟩ := List.mem_map.mp hm
  cases t with
  | inl f => fin_cases f <;> simp [Allowed, signedMove, positiveMove, faceMove]
  | inr ax => simp [Allowed, signedMove, positiveMove, sliceMove]
