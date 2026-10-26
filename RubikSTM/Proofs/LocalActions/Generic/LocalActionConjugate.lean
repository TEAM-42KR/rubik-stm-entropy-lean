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
theorem proof_RubikLocal_Generic_local_action_conjugate {n : ℕ} (a b : Fin n) (q τ : Perm)
    (p g : Equiv.Perm (Sticker n))
    (hp : ∀ i, p (RubikGeometry.lab a b i) = RubikGeometry.lab a b (q i))
    (hg : LocalAction a b τ g) : LocalAction a b (q * τ * q⁻¹) (p * g * p⁻¹) := by
  constructor
  · intro i
    simp only [Equiv.Perm.mul_apply, RubikGeometry.T.inverse_on_labels _ _ _ hp, hg.1, hp]
  · intro s hs
    have hout : p⁻¹ s ∉ Set.range (RubikGeometry.lab a b) := by
      rintro ⟨i, hi⟩
      apply hs
      refine ⟨q i, ?_⟩
      rw [← hp i, hi]
      exact p.apply_symm_apply s
    simp only [Equiv.Perm.mul_apply, hg.2 _ hout]
    exact p.apply_symm_apply s
