import RubikSTM.Definitions.Geometry.StmGraph
set_option autoImplicit false

namespace RubikBand
open Rubik

def Band {n : ℕ} (a : Fin n) (s : Sticker n) : Prop :=
  ∃ q : Axis, coordinate s.val.1 q = a ∨ coordinate s.val.1 q = a.rev

def wordPerm {n : ℕ} (w : List (Move n)) : Equiv.Perm (Sticker n) :=
  (w.map movePermutation).reverse.prod

def faceDeletion {n : ℕ} (a : Fin n) (w : List (Move n)) : List (Move n) :=
  w.filter (fun m => decide (m.2.1 ≠ a ∧ m.2.1 ≠ a.rev))

def AllowedControl {n : ℕ} (a : Fin n) (w : List (Move n)) : Prop :=
  ∀ m ∈ w, m.2.1.val = 0 ∨ m.2.1.val = n-1 ∨ m.2.1 = a ∨ m.2.1 = a.rev

def StrictControl {n : ℕ} (a : Fin n) (w : List (Move n)) : Prop :=
  AllowedControl a w ∧ wordPerm (faceDeletion a w) = 1

def Bands {n : ℕ} (Y : Finset (Fin n)) (s : Sticker n) : Prop :=
  ∃ b ∈ Y, Band b s

def parallelBaseline {n : ℕ} (q : Axis) (Y : Finset (Fin n)) : Equiv.Perm (Sticker n) :=
  ((Y.sort (· ≤ ·)).map (sliceQuarter n q)).reverse.prod

end RubikBand
