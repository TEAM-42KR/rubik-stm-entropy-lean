import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open Rubik RubikGeometry
theorem proof_RubikGeometry_T_range_iff {α β : Type*} (f : β → α) (p : Equiv.Perm α) (q : Equiv.Perm β)
    (h : ∀ i, p (f i) = f (q i)) (s : α) :
    p s ∈ Set.range f ↔ s ∈ Set.range f := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨q⁻¹ i, p.injective ?_⟩
    rw [h]
    simpa using hi
  · rintro ⟨i, rfl⟩
    exact ⟨q i, (h i).symm⟩
