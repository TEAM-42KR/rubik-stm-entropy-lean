import RubikSTM.Definitions.Orbits.SwapPhi
import RubikSTM.Lemmas.Orbits.FlipLabel
set_option autoImplicit false

theorem proof_RubikOrbit_minusRange {n : ℕ} {a b : Fin n} (hg : RubikGeometry.Generic n a b)
  (hb : 0 < b.val ∧ b.val + 1 < n) :
  Set.range (RubikOrbit.minusLab a b hb) = Set.range (RubikGeometry.lab b a) := by
  apply Set.Subset.antisymm
  · rintro s ⟨i, rfl⟩
    exact ⟨RubikOrbit.swapPhi i, (RubikOrbit.flipLabel hg hb i).symm⟩
  · rintro s ⟨i, rfl⟩
    refine ⟨RubikOrbit.swapPhi.symm i, ?_⟩
    rw [RubikOrbit.flipLabel hg hb, Equiv.apply_symm_apply]

#print axioms proof_RubikOrbit_minusRange
