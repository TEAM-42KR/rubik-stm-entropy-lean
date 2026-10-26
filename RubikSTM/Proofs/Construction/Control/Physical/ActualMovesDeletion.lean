import Mathlib
import RubikSTM.Definitions.Construction.Control.Physical.ActualMoves
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Lemmas.Construction.Control.Physical.ChronologicalAlgebra
import RubikSTM.Lemmas.Construction.Control.Physical.SignedMoveEval
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open Rubik RubikConstruction.Control RubikConstruction.Control.Physical
theorem proof_RubikConstruction_Control_Physical_actual_moves_deletion {n : ℕ} (a : Fin n)
    (ha : 1 ≤ a.val) (has : 2 * a.val + 2 ≤ n) (letters : List SignedLetter) :
    chronological (faceOnlyMoves a (actualMoves a letters)) = faceOnlyEval a (FreeGroup.mk letters) := by
  have halow : a ≠ low a := by
    intro h
    have hv := congrArg Fin.val h
    simp only [low, Fin.val_mk] at hv
    omega
  have hahigh : a ≠ high a := by
    intro h
    have hv := congrArg Fin.val h
    simp only [high, Fin.val_mk] at hv
    omega
  have happ (u v : List (Move n)) : chronological (u ++ v) = chronological v * chronological u := by
    induction u with
    | nil => simp [chronological]
    | cons m u ih => simp [chronological, ih, mul_assoc]
  have hletter (t : SignedLetter) :
      chronological (faceOnlyMoves a [signedMove a t]) = faceOnlyEval a (FreeGroup.mk [t]) := by
    rcases t with ⟨t, s⟩
    cases t with
    | inl f =>
      have hkeep : faceOnlyMoves a [signedMove a (Sum.inl f, s)] = [signedMove a (Sum.inl f, s)] := by
        fin_cases f <;> simp [faceOnlyMoves, signedMove, positiveMove, faceMove]
      rw [hkeep]
      change movePermutation (signedMove a (Sum.inl f, s)) = _
      rw [signed_move_eval]
      cases s <;> simp [faceOnlyEval, physicalFaceEval, deletion, FreeGroup.lift_mk, physicalAtom]
    | inr ax =>
      cases s <;> simp [faceOnlyMoves, signedMove, positiveMove, sliceMove,
        halow, hahigh, chronological, faceOnlyEval, physicalFaceEval, deletion, FreeGroup.lift_mk]
  induction letters with
  | nil =>
    change (1 : Equiv.Perm (Sticker n)) = faceOnlyEval a 1
    rw [map_one]
  | cons t letters ih =>
    rw [show actualMoves a (t :: letters) = actualMoves a letters ++ [signedMove a t] by simp [actualMoves]]
    change chronological ((actualMoves a letters ++ [signedMove a t]).filter _) = _
    rw [List.filter_append, happ]
    change chronological (faceOnlyMoves a [signedMove a t]) *
      chronological (faceOnlyMoves a (actualMoves a letters)) = _
    rw [hletter, ih, ← map_mul]
    rfl
