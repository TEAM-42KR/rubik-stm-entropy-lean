import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open Rubik RubikGeometry
theorem proof_RubikGeometry_T_commutator_fixed {α : Type*} (O : Set α) (p q : Equiv.Perm α)
    (hp : ∀ s, p s ∈ O ↔ s ∈ O) (hq : ∀ s, q s ∈ O ↔ s ∈ O)
    (hdisj : ∀ s, p s ≠ s → q s ≠ s → s ∈ O) (s : α) (hs : s ∉ O) :
    (p * q * p⁻¹ * q⁻¹) s = s := by
  have hc : ∀ x, x ∉ O → p (q x) = q (p x) := by
    intro x hx
    by_cases hpx : p x = x
    · by_cases hqx : q x = x
      · simp [hpx, hqx]
      · have hqout : q x ∉ O := fun h => hx ((hq x).mp h)
        have hqq : q (q x) ≠ q x := fun h => hqx (q.injective h)
        have hpq : p (q x) = q x := by
          by_contra h
          exact hqout (hdisj (q x) h hqq)
        simp [hpx, hpq]
    · have hqx : q x = x := by
        by_contra h
        exact hx (hdisj x hpx h)
      have hpout : p x ∉ O := fun h => hx ((hp x).mp h)
      have hpp : p (p x) ≠ p x := fun h => hpx (p.injective h)
      have hqp : q (p x) = p x := by
        by_contra h
        exact hpout (hdisj (p x) hpp h)
      simp [hqx, hqp]
  have hqout : q⁻¹ s ∉ O := by
    intro h
    apply hs
    have := (hq (q⁻¹ s)).mpr h
    simpa using this
  have hpout : p⁻¹ (q⁻¹ s) ∉ O := by
    intro h
    apply hqout
    have := (hp (p⁻¹ (q⁻¹ s))).mpr h
    simpa using this
  change p (q (p⁻¹ (q⁻¹ s))) = s
  rw [hc _ hpout]
  simp
