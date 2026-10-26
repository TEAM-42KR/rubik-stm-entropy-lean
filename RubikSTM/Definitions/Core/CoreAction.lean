import RubikSTM.Definitions.Core.Project
set_option autoImplicit false

open RubikCore

theorem RubikCore.Internal.isLevel_rev {n : ℕ} (x : Fin n) : IsLevel x.rev ↔ IsLevel x := by
  have h {y : Fin n} : IsLevel y → IsLevel y.rev := by
    intro hy
    rcases hy with h0 | h1 | hm
    · right; left
      simp [Fin.rev, h0]
    · left
      simp only [Fin.rev, h1]
      omega
    · right; right
      rw [Fin.rev_rev]
      exact hm.symm
  exact ⟨fun hh => by simpa using h hh, h⟩

open Rubik RubikCore

theorem RubikCore.Internal.rotation_core {n : ℕ} (a : Axis) (s : Sticker n) :
    IsCore (surfaceRotation n a s) ↔ IsCore s := by
  have hcore (t : Sticker n) : IsCore t ↔
      IsLevel t.val.1.1 ∧ IsLevel t.val.1.2.1 ∧ IsLevel t.val.1.2.2 := by
    simp only [IsCore]
    constructor
    · intro h
      exact ⟨h 0, h 1, h 2⟩
    · rintro ⟨h0, h1, h2⟩ i
      fin_cases i <;> assumption
  rw [hcore, hcore]
  fin_cases a <;>
    simp [surfaceRotation, rawRotation, coordinateRotation, RubikCore.Internal.isLevel_rev,
      and_assoc, and_left_comm, and_comm]

open Rubik RubikCore

theorem RubikCore.Internal.slice_core {n : ℕ} (a : Axis) (l : Fin n) (s : Sticker n) :
    IsCore (sliceQuarter n a l s) ↔ IsCore s := by
  by_cases h : coordinate s.val.1 a = l
  · simpa [sliceQuarter, h] using RubikCore.Internal.rotation_core a s
  · simp [sliceQuarter, h]

open Rubik RubikCore

theorem RubikCore.Internal.move_core {n : ℕ} (m : Move n) (s : Sticker n) :
    IsCore (movePermutation m s) ↔ IsCore s := by
  have hp (k : ℕ) (t : Sticker n) :
      IsCore ((sliceQuarter n m.1 m.2.1 ^ k) t) ↔ IsCore t := by
    induction k generalizing t with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ, Equiv.Perm.mul_apply]
      exact (ih _).trans (RubikCore.Internal.slice_core m.1 m.2.1 t)
  exact hp _ _

namespace RubikCore
open Rubik

def coreMove {n : ℕ} (m : Move n) : Equiv.Perm (CoreSticker n) :=
  (movePermutation m).subtypeEquiv (fun s => (Internal.move_core m s).symm)

def coreAction {n : ℕ} (m : Move n) : Equiv.Perm (CoreColouring n) :=
  Equiv.arrowCongr (coreMove m) (Equiv.refl Colour)

def cleanupBound : ℕ := 6 ^ 162

end RubikCore

#print axioms RubikCore.coreAction
