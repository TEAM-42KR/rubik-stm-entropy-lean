import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Lemmas.OrbitGeometry.MoveLab
import RubikSTM.Lemmas.OrbitGeometry.T.InverseOnLabels
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open Rubik RubikGeometry
open RubikGeometry.T
theorem proof_RubikGeometry_commElt_lab {n : ℕ} {a b : Fin n} (hg : Generic n a b) (i : Fin 24) :
    commElt a b (lab a b i) = lab a b (t0 i) := by
  have hm := move_lab hg
  have hinv : ∀ k i, (movePermutation (genMove a b k))⁻¹ (lab a b i) =
      lab a b ((genPerm k)⁻¹ i) :=
    fun k i => T.inverse_on_labels _ _ _ (hm k) i
  simp only [commElt, t0, mul_inv_rev, inv_inv, Equiv.Perm.mul_apply, hm, hinv]
