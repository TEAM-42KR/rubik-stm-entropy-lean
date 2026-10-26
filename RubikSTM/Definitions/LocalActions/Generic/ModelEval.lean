import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Definitions.Construction.Control.Physical.ActualMoves
set_option autoImplicit false

namespace RubikLocal.Generic
open Rubik RubikGeometry

abbrev Label := Fin 24
abbrev Perm := Equiv.Perm Label
abbrev Token := Perm × Bool
abbrev ControlLetters := List RubikConstruction.Control.Physical.SignedLetter

def conjugateThree (q : Perm) : Perm := q * RubikGeometry.t0 * q⁻¹

def modelEval : FreeGroup Perm →* Perm := FreeGroup.lift conjugateThree

def tokenPerm (t : Token) : Perm :=
  if t.2 then conjugateThree t.1 else (conjugateThree t.1)⁻¹

def evalTokens (tokens : List Token) : Perm := (tokens.map tokenPerm).prod

def LocalAction {n : ℕ} (a b : Fin n) (τ : Perm)
    (g : Equiv.Perm (Sticker n)) : Prop :=
  (∀ i, g (RubikGeometry.lab a b i) = RubikGeometry.lab a b (τ i)) ∧
    ∀ s, s ∉ Set.range (RubikGeometry.lab a b) → g s = s

def tSignedMove {n : ℕ} (a b : Fin n) (t : Fin 8 × Bool) : Move n :=
  let m := RubikGeometry.genMove a b t.1
  (m.1, m.2.1, if t.2 then 0 else 2)

def tActualMoves {n : ℕ} (a b : Fin n) (ts : List (Fin 8 × Bool)) : List (Move n) :=
  ts.reverse.map (tSignedMove a b)

def primitiveLetters : List (Fin 8 × Bool) :=
  [(6, false), (5, true), (6, true), (7, true),
    (6, false), (5, false), (6, true), (7, false)]

def primitiveMoves {n : ℕ} (a b : Fin n) (s : Bool) : List (Move n) :=
  tActualMoves a b (if s then primitiveLetters else FreeGroup.invRev primitiveLetters)

def conjugateMoves {n : ℕ} (a b : Fin n) (cw : Perm → ControlLetters)
    (t : Token) : List (Move n) :=
  RubikConstruction.Control.Physical.actualMoves a (FreeGroup.invRev (cw t.1)) ++
    primitiveMoves a b t.2 ++ RubikConstruction.Control.Physical.actualMoves a (cw t.1)

def realizeTokens {n : ℕ} (a b : Fin n) (cw : Perm → ControlLetters) :
    List Token → List (Move n)
  | [] => []
  | t :: ts => realizeTokens a b cw ts ++ conjugateMoves a b cw t

end RubikLocal.Generic
