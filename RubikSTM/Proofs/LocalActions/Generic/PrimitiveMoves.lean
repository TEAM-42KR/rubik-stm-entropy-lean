import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Definitions.LocalActions.Generic.ModelEval
import RubikSTM.Lemmas.Construction.Control.Physical.QuarterInverse
import RubikSTM.Lemmas.Construction.Control.Physical.ChronologicalAlgebra
import RubikSTM.Lemmas.OrbitGeometry.CommEltLab
import RubikSTM.Lemmas.OrbitGeometry.CommEltOff
import RubikSTM.Lemmas.LocalActions.Generic.LocalActionInv
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open Rubik RubikGeometry
open RubikLocal.Generic RubikConstruction.Control.Physical
theorem proof_RubikLocal_Generic_primitive_moves {n : ℕ} (a b : Fin n) (hg : RubikGeometry.Generic n a b) (s : Bool) :
    (primitiveMoves a b s).length = 8 ∧
      LocalAction a b (if s then RubikGeometry.t0 else RubikGeometry.t0⁻¹)
        (chronological (primitiveMoves a b s)) := by
  let h : FreeGroup (Fin 8) →* Equiv.Perm (Sticker n) :=
    FreeGroup.lift (fun k => movePermutation (RubikGeometry.genMove a b k))
  have hsign (t : Fin 8 × Bool) : movePermutation (tSignedMove a b t) =
      if t.2 then movePermutation (RubikGeometry.genMove a b t.1)
      else (movePermutation (RubikGeometry.genMove a b t.1))⁻¹ := by
    rcases t with ⟨k, s⟩
    have hquarter :
        ((RubikGeometry.genMove a b k).1, (RubikGeometry.genMove a b k).2.1, (0 : Fin 3)) = RubikGeometry.genMove a b k := by
      fin_cases k <;> rfl
    cases s
    · change movePermutation ((RubikGeometry.genMove a b k).1, (RubikGeometry.genMove a b k).2.1, 2) = _
      rw [quarter_inverse, hquarter]
      rfl
    · simpa only [tSignedMove, if_true] using congrArg movePermutation hquarter
  have heval (ts : List (Fin 8 × Bool)) :
      chronological (tActualMoves a b ts) = h (FreeGroup.mk ts) := by
    rw [chronological_algebra]
    simp only [tActualMoves, ← List.map_reverse, List.reverse_reverse, List.map_map]
    simp [h, FreeGroup.lift_mk, hsign, Function.comp_def, cond_eq_ite]
  have hprim : h (FreeGroup.mk primitiveLetters) = RubikGeometry.commElt a b := by
    simp [h, primitiveLetters, FreeGroup.lift_mk, RubikGeometry.commElt, mul_inv_rev, mul_assoc]
  have heq : chronological (primitiveMoves a b s) =
      if s then RubikGeometry.commElt a b else (RubikGeometry.commElt a b)⁻¹ := by
    cases s
    · simp only [primitiveMoves, Bool.false_eq_true, if_false, heval, ← FreeGroup.inv_mk, map_inv, hprim]
    · simp only [primitiveMoves, if_true, heval, hprim]
  have hlocal : LocalAction a b RubikGeometry.t0 (RubikGeometry.commElt a b) :=
    ⟨RubikGeometry.commElt_lab hg, RubikGeometry.commElt_off hg⟩
  constructor
  · cases s <;> simp [primitiveMoves, tActualMoves, primitiveLetters, FreeGroup.invRev_length]
  · rw [heq]
    cases s
    · exact local_action_inv a b _ _ hlocal
    · exact hlocal
