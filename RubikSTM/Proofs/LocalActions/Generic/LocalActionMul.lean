import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Definitions.LocalActions.Generic.ModelEval
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open Rubik RubikGeometry
open RubikLocal.Generic RubikConstruction.Control.Physical
theorem proof_RubikLocal_Generic_local_action_mul {n : ℕ} (a b : Fin n) (τ υ : Perm)
    (g h : Equiv.Perm (Sticker n)) (hg : LocalAction a b τ g) (hh : LocalAction a b υ h) :
    LocalAction a b (τ * υ) (g * h) := by
  constructor
  · intro i
    simp only [Equiv.Perm.mul_apply, hh.1, hg.1]
  · intro s hs
    simp only [Equiv.Perm.mul_apply, hh.2 s hs, hg.2 s hs]
