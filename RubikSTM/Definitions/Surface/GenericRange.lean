import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Definitions.Core.Project
import RubikSTM.Definitions.Wings.FaceOnlyEval
import RubikSTM.Definitions.ExceptionalCentres.DiagonalThreeCycle
set_option autoImplicit false

namespace RubikGlobal
open Rubik

abbrev I (n : ℕ) := Fin ((n - 2) / 2)
abbrev Q (n : ℕ) := {p : I n × I n // p.1 ≠ p.2}
abbrev ExceptionalIndex (n : ℕ) := I n × Fin 3

def depth {n : ℕ} (i : I n) : Fin n :=
  ⟨i.val + 1, by have := i.isLt; omega⟩

def label {n : ℕ} (p : Q n) : Fin 24 → Sticker n :=
  RubikGeometry.lab (depth p.val.1) (depth p.val.2)

def GenericRange {n : ℕ} (p : Q n) : Set (Sticker n) := Set.range (label p)

def WingRange {n : ℕ} (i : I n) : Set (Sticker n) :=
  {s | ∃ l : Fin 24, ∃ b : Fin 2, RubikWing.lab (depth i) l b = s}

def DiagonalRange {n : ℕ} (i : I n) : Set (Sticker n) :=
  Set.range (RubikGeometry.lab (depth i) (depth i))

def CrossRange {n : ℕ} (i : I n) : Set (Sticker n) :=
  {s | ∃ m : Fin n, m.rev = m ∧ s ∈ Set.range (RubikGeometry.lab (depth i) m)}

def ExceptionalRange {n : ℕ} (e : ExceptionalIndex n) : Set (Sticker n) :=
  if e.2 = 0 then WingRange e.1 else if e.2 = 1 then DiagonalRange e.1 else CrossRange e.1

def tangent {n : ℕ} (s : RawSticker n) : Fin n × Fin n :=
  if s.2.1 = 0 then
    if s.2.2 then (s.1.2.1, s.1.2.2) else (s.1.2.1, s.1.2.2.rev)
  else if s.2.1 = 1 then
    if s.2.2 then (s.1.1, s.1.2.2.rev) else (s.1.1, s.1.2.2)
  else if s.2.2 then (s.1.1, s.1.2.1) else (s.1.2.1, s.1.1)

def depths {n : ℕ} (s : RawSticker n) : ℕ × ℕ :=
  let (u,v) := tangent s
  if 2 * u.val < n then
    if 2 * v.val < n then (u.val, v.val) else (v.rev.val, u.val)
  else if 2 * v.val < n then (v.val, u.rev.val) else (u.rev.val, v.rev.val)

def CentreFrame {n : ℕ} (a b : Fin n) (s : Sticker n) : Prop :=
  let t := tangent s.val
  ((t.1 = a ∨ t.1 = a.rev) ∧ (t.2 = b ∨ t.2 = b.rev)) ∨
    ((t.1 = b ∨ t.1 = b.rev) ∧ (t.2 = a ∨ t.2 = a.rev))

def WingFrame {n : ℕ} (a : Fin n) (s : Sticker n) : Prop :=
  let t := tangent s.val
  (((t.1.val = 0 ∨ t.1.val = n-1)) ∧ (t.2 = a ∨ t.2 = a.rev)) ∨
    ((t.1 = a ∨ t.1 = a.rev) ∧ ((t.2.val = 0 ∨ t.2.val = n-1)))

def IsCentre {n : ℕ} (s : Sticker n) : Prop :=
  0 < (tangent s.val).1.val ∧ (tangent s.val).1.val + 1 < n ∧
    0 < (tangent s.val).2.val ∧ (tangent s.val).2.val + 1 < n

end RubikGlobal
