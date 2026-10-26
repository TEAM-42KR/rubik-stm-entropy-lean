import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Lemmas.OrbitGeometry.MoveLab
import RubikSTM.Lemmas.OrbitGeometry.T.InverseOnLabels
import RubikSTM.Lemmas.OrbitGeometry.T.RangeIff
import RubikSTM.Lemmas.OrbitGeometry.T.CommutatorFixed
import RubikSTM.Lemmas.OrbitGeometry.T.SupportIntersection
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open Rubik RubikGeometry
open RubikGeometry.T
theorem proof_RubikGeometry_commElt_off {n : ℕ} {a b : Fin n} (hg : Generic n a b) (s : Sticker n)
    (hs : s ∉ Set.range (lab a b)) : commElt a b s = s := by
  have hm := move_lab hg
  have hinv : ∀ k i, (movePermutation (genMove a b k))⁻¹ (lab a b i) =
      lab a b ((genPerm k)⁻¹ i) :=
    fun k i => T.inverse_on_labels _ _ _ (hm k) i
  let P := (movePermutation (genMove a b 6))⁻¹ * movePermutation (genMove a b 5) *
    movePermutation (genMove a b 6)
  let Q := movePermutation (genMove a b 7)
  let p := (genPerm 6)⁻¹ * genPerm 5 * genPerm 6
  have hP : ∀ i, P (lab a b i) = lab a b (p i) := by
    intro i
    simp only [P, p, Equiv.Perm.mul_apply, hm, hinv]
  have hQ : ∀ i, Q (lab a b i) = lab a b (genPerm 7 i) := hm 7
  change (P * Q * P⁻¹ * Q⁻¹) s = s
  exact T.commutator_fixed (Set.range (lab a b)) P Q
    (T.range_iff _ _ _ hP) (T.range_iff _ _ _ hQ) (T.support_intersection hg) s hs
