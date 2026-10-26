import Mathlib
import RubikSTM.Definitions.Construction.Control.Physical.ActualMoves
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Lemmas.Construction.Control.AllNActionBridge
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open Rubik RubikConstruction.Control RubikConstruction.Control.Physical
theorem proof_RubikConstruction_Control_Physical_word_action {n : ℕ} (a b : Fin n)
    (ha : 1 ≤ a.val) (hb : 1 ≤ b.val)
    (has : 2 * a.val + 2 ≤ n) (hbs : 2 * b.val + 2 ≤ n) (hab : a ≠ b)
    (w : Word) (i : Fin 24) :
    physicalEval a w (lab a b i) = lab a b (finiteEval w i) := by
  have hbridge := all_n_action_bridge n a b ha hb has hbs hab
  have hword (w : Word) : ∀ i,
      physicalEval a w (lab a b i) = lab a b (finiteEval w i) := by
    refine FreeGroup.induction_on w ?_ ?_ ?_ ?_
    · intro i
      simp
    · intro t i
      simpa [physicalEval, finiteEval] using hbridge t i
    · intro t ht i
      rw [map_inv, map_inv]
      apply Equiv.Perm.inv_eq_iff_eq.mpr
      simpa using (ht ((finiteEval (FreeGroup.of t))⁻¹ i)).symm
    · intro u v hu hv i
      rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hv, hu]
  exact hword w i
