import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Definitions.Construction.Control.Physical.ActualMoves
import RubikSTM.Definitions.Bands.Band
set_option autoImplicit false

namespace RubikOBTM.Band
open Rubik
abbrev Label := Fin 24
abbrev Perm := Equiv.Perm Label
abbrev PairPerm := Perm × Perm
abbrev RowLetters := List RubikConstruction.Control.Physical.SignedLetter

structure Admissible (n : ℕ) (a u v : Fin n) : Prop where
  row_pos : 1 ≤ a.val
  row_small : 2 * a.val + 2 ≤ n
  lower_pos : 1 ≤ u.val
  ordered : u.val ≤ v.val
  upper_small : 2 * v.val + 2 ≤ n
  row_outside : a.val < u.val ∨ v.val < a.val

def InInterval {n : ℕ} (u v d : Fin n) : Prop := u.val ≤ d.val ∧ d.val ≤ v.val

def plus {n : ℕ} (a d : Fin n) : Label → Sticker n := RubikConstruction.Control.lab a d

def minus {n : ℕ} (a d : Fin n) : Label → Sticker n := RubikConstruction.Control.lab a d.rev

def PairedRange {n : ℕ} (a u v : Fin n) : Set (Sticker n) :=
  {s | ∃ d : Fin n, InInterval u v d ∧
    (s ∈ Set.range (plus a d) ∨ s ∈ Set.range (minus a d))}

def ColumnBand {n : ℕ} (u v : Fin n) (s : Sticker n) : Prop :=
  ∃ d : Fin n, InInterval u v d ∧ RubikBand.Band d s

def wordPerm {n : ℕ} (w : List (RubikOBTM.BlockMove n)) : Equiv.Perm (Sticker n) :=
  (w.map RubikOBTM.blockPermutation).reverse.prod

def CleanAction {n : ℕ} (a u v : Fin n) (p : PairPerm) (P : Equiv.Perm (Sticker n)) : Prop :=
  (∀ d : Fin n, InInterval u v d → ∀ i : Label,
    P (plus a d i) = plus a d (p.1 i) ∧
    P (minus a d i) = minus a d (p.2 i)) ∧
  ∀ s : Sticker n, s ∉ PairedRange a u v → P s = s

def Bplus : Perm := Equiv.swap 0 16 * Equiv.swap 16 23 * Equiv.swap 23 7
def Bminus : Perm := Equiv.swap 3 4 * Equiv.swap 4 20 * Equiv.swap 20 19

end RubikOBTM.Band
