import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Definitions.LocalActions.Generic.ModelEval
import RubikSTM.Lemmas.LocalActions.Generic.PrimitiveMoves
import RubikSTM.Lemmas.LocalActions.Generic.LocalActionConjugate
import RubikSTM.Lemmas.LocalActions.Generic.ChronologicalAppend
import RubikSTM.Lemmas.Construction.Control.Physical.ActualMovesEval
import RubikSTM.Lemmas.Construction.Control.Physical.WordAction
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open Rubik RubikGeometry
open RubikLocal.Generic RubikConstruction.Control.Physical
theorem proof_RubikLocal_Generic_conjugate_bounded (L : ℕ) (cw : Perm → ControlLetters)
    (hcw : ∀ q, (cw q).length ≤ L ∧ RubikConstruction.Control.finiteEval (FreeGroup.mk (cw q)) = q)
    {n : ℕ} (a b : Fin n) (hg : RubikGeometry.Generic n a b) (t : Token) :
    (conjugateMoves a b cw t).length ≤ 2 * L + 8 ∧
      LocalAction a b (tokenPerm t) (chronological (conjugateMoves a b cw t)) := by
  let P := RubikConstruction.Control.physicalEval a (FreeGroup.mk (cw t.1))
  have hP : ∀ i, P (RubikGeometry.lab a b i) = RubikGeometry.lab a b (t.1 i) := by
    intro i
    change RubikConstruction.Control.physicalEval a (FreeGroup.mk (cw t.1)) (RubikConstruction.Control.lab a b i) =
      RubikConstruction.Control.lab a b (t.1 i)
    simpa only [(hcw t.1).2] using
      word_action a b hg.one_le_a hg.one_le_b hg.a_small hg.b_small hg.ne (FreeGroup.mk (cw t.1)) i
  have hprim := primitive_moves a b hg t.2
  have heq : chronological (conjugateMoves a b cw t) =
      P * chronological (primitiveMoves a b t.2) * P⁻¹ := by
    simp only [conjugateMoves, chronological_append, actual_moves_eval,
      ← FreeGroup.inv_mk, map_inv]
    rfl
  constructor
  · simp only [conjugateMoves, List.length_append, RubikConstruction.Control.Physical.actualMoves,
      List.length_map, List.length_reverse, FreeGroup.invRev_length, hprim.1]
    have := (hcw t.1).1
    omega
  · rw [heq]
    have hlocal := local_action_conjugate a b t.1
      (if t.2 then RubikGeometry.t0 else RubikGeometry.t0⁻¹) P
      (chronological (primitiveMoves a b t.2)) hP hprim.2
    have htoken : tokenPerm t = t.1 * (if t.2 then RubikGeometry.t0 else RubikGeometry.t0⁻¹) * t.1⁻¹ := by
      rcases t with ⟨q, s⟩
      cases s <;> simp [RubikLocal.Generic.tokenPerm, conjugateThree, mul_inv_rev, mul_assoc]
    rw [htoken]
    exact hlocal
