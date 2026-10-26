import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Definitions.LocalActions.Generic.ModelEval
import RubikSTM.Lemmas.OrbitGeometry.T.InverseOnLabels
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open Rubik RubikGeometry
open RubikGeometry.T
open RubikLocal.Generic RubikConstruction.Control.Physical
theorem proof_RubikLocal_Generic_local_action_inv {n : ℕ} (a b : Fin n) (τ : Perm)
    (g : Equiv.Perm (Sticker n)) (hg : LocalAction a b τ g) :
    LocalAction a b τ⁻¹ g⁻¹ := by
  constructor
  · exact RubikGeometry.T.inverse_on_labels _ _ _ hg.1
  · intro s hs
    rw [Equiv.Perm.inv_eq_iff_eq, hg.2 s hs]
