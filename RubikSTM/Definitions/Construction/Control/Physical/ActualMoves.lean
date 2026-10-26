import Mathlib
import RubikSTM.Definitions.Construction.Control.K
set_option autoImplicit false

namespace RubikConstruction.Control.Physical
open Rubik

abbrev SignedLetter := Alphabet × Bool

def positiveMove {n : ℕ} (a : Fin n) : Alphabet → Move n :=
  Sum.elim (faceMove a) (sliceMove a)

def signedMove {n : ℕ} (a : Fin n) (t : SignedLetter) : Move n :=
  let m := positiveMove a t.1
  (m.1, m.2.1, if t.2 then 0 else 2)

def actualMoves {n : ℕ} (a : Fin n) (letters : List SignedLetter) : List (Move n) :=
  letters.reverse.map (signedMove a)

def chronological {n : ℕ} : List (Move n) → Equiv.Perm (Sticker n)
  | [] => 1
  | m :: ms => chronological ms * movePermutation m

def Allowed {n : ℕ} (a : Fin n) (m : Move n) : Prop :=
  m.2.1 = low a ∨ m.2.1 = high a ∨ m.2.1 = a

def faceOnlyMoves {n : ℕ} (a : Fin n) (ms : List (Move n)) : List (Move n) :=
  ms.filter (fun m => m.2.1 = low a ∨ m.2.1 = high a)

end RubikConstruction.Control.Physical
