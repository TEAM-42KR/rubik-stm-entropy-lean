import RubikSTM.Definitions.OBTM.Band.SlabWord
import RubikSTM.Lemmas.Construction.Control.Physical.WordAction
import RubikSTM.Lemmas.OBTM.Band.RowFaceMinus
import RubikSTM.Lemmas.OBTM.Band.RowSliceMinus
set_option autoImplicit false
open Rubik RubikConstruction.Control RubikOBTM.Band
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

theorem proof_RubikOBTM_Band_row_action_both {n : ℕ} (a d : Fin n)
    (ha : 1 ≤ a.val) (hd : 1 ≤ d.val) (has : 2*a.val+2 ≤ n)
    (hds : 2*d.val+2 ≤ n) (had : a ≠ d) (w : Word) (i : Fin 24) :
    (physicalEval a w (plus a d i) = plus a d (finiteEval w i)) ∧
    (physicalEval a w (minus a d i) = minus a d (finiteEval w i)) := by
  have hb : ActionBridge a d.rev := by
    intro t j
    cases t with
    | inl f => exact row_face_minus a d ha hd has hds had f j
    | inr ax => exact row_slice_minus a d ha hd has hds had ax j
  have hword (w : Word) : ∀ j,
      physicalEval a w (lab a d.rev j) = lab a d.rev (finiteEval w j) := by
    refine FreeGroup.induction_on w ?_ ?_ ?_ ?_
    · intro j; simp
    · intro t j
      simpa [physicalEval,finiteEval] using hb t j
    · intro t ht j
      rw [map_inv,map_inv]
      apply Equiv.Perm.inv_eq_iff_eq.mpr
      simpa using (ht ((finiteEval (FreeGroup.of t))⁻¹ j)).symm
    · intro x y hx hy j
      rw [map_mul,map_mul,Equiv.Perm.mul_apply,Equiv.Perm.mul_apply,hy,hx]
  exact ⟨Physical.word_action a d ha hd has hds had w i,hword w i⟩
