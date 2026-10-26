import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Lemmas.OrbitGeometry.T.QuarterSupport
import RubikSTM.Lemmas.OrbitGeometry.T.IntersectionSticker
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open Rubik RubikGeometry
open RubikGeometry.T
theorem proof_RubikGeometry_T_support_intersection {n : ℕ} {a b : Fin n} (hg : Generic n a b) (s : Sticker n)
    (hp : ((movePermutation (genMove a b 6))⁻¹ * movePermutation (genMove a b 5) *
      movePermutation (genMove a b 6)) s ≠ s)
    (hq : movePermutation (genMove a b 7) s ≠ s) : s ∈ Set.range (lab a b) := by
  let X := movePermutation (genMove a b 6)
  let F := movePermutation (genMove a b 5)
  have hz : s.val.1.2.2 = b.rev := by
    have hq' : movePermutation (2, b.rev, 0) s ≠ s := by simpa [genMove] using hq
    simpa [coordinate] using quarter_support 2 b.rev s hq'
  have hF : F (X s) ≠ X s := by
    intro h
    apply hp
    change X⁻¹ (F (X s)) = s
    rw [h]
    simp
  have hface : coordinate (X s).val.1 2 = hi a := by
    apply quarter_support 2 (hi a) (X s)
    simpa [F, genMove] using hF
  have hbr : b.rev ≠ hi a := by
    intro h
    have hv := congrArg Fin.val h
    simp [hi, Fin.rev] at hv
    have := hg.one_le_b
    have := b.isLt
    omega
  have hx : s.val.1.1 = a := by
    by_contra hxa
    have hfix : X s = s := by
      simp [X, genMove, movePermutation, sliceQuarter, coordinate, hxa]
    apply hbr
    simpa [coordinate, hfix, hz] using hface
  have hXraw : (X s).val.1.2.2 = s.val.1.2.1 := by
    simp [X, genMove, movePermutation, sliceQuarter, coordinate, hx,
      surfaceRotation, rawRotation, coordinateRotation]
  have hy : s.val.1.2.1 = hi a := by
    rw [← hXraw]
    simpa [coordinate] using hface
  exact ⟨4, (intersection_sticker hg s hx hy hz).symm⟩
