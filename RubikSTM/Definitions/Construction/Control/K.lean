import Mathlib
import RubikSTM.Definitions.Geometry.StmGraph
set_option autoImplicit false

namespace RubikConstruction.Control
open Rubik

abbrev Label := Fin 24
abbrev Alphabet := Sum (Fin 6) (Fin 3)
abbrev Word := FreeGroup Alphabet

def low {n : ℕ} (a : Fin n) : Fin n := ⟨0, by have := a.isLt; omega⟩
def high {n : ℕ} (a : Fin n) : Fin n := ⟨n - 1, by have := a.isLt; omega⟩

section Labels
variable {n : ℕ}
def posTable (a b : Fin n) : Fin 24 → Coord n :=
  ![(high a, b.rev, a),
    (high a, b, a.rev),
    (high a, a.rev, b.rev),
    (high a, a, b),
    (a, high a, b.rev),
    (a, b, high a),
    (b.rev, a, high a),
    (a.rev, b.rev, high a),
    (b, a.rev, high a),
    (b, low a, a.rev),
    (low a, b.rev, a.rev),
    (low a, b, a),
    (b.rev, high a, a.rev),
    (a.rev, high a, b),
    (b, high a, a),
    (low a, a, b.rev),
    (low a, a.rev, b),
    (a.rev, low a, b.rev),
    (b.rev, low a, a),
    (a, low a, b),
    (b, a, low a),
    (a.rev, b, low a),
    (b.rev, a.rev, low a),
    (a, b.rev, low a)]

def normalTable : Fin 24 → Normal :=
  ![(0, true), (0, true), (0, true), (0, true), (1, true), (2, true), (2, true), (2, true), (2, true), (1, false), (0, false), (0, false), (1, true), (1, true), (1, true), (0, false), (0, false), (1, false), (1, false), (1, false), (2, false), (2, false), (2, false), (2, false)]

def rawLab (a b : Fin n) (i : Fin 24) : RawSticker n := (posTable a b i, normalTable i)

def lab (a b : Fin n) (i : Fin 24) : Sticker n := ⟨rawLab a b i, by
  fin_cases i <;> simp [rawLab, posTable, normalTable, IsSurface, coordinate, low, high]⟩

end Labels

def face0 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 16, 12, 13, 14, 11, 10, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 16, 15, 12, 13, 14, 10, 11, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def face1 : Equiv.Perm (Fin 24) where
  toFun := ![2, 3, 1, 0, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![3, 2, 0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def face2 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 17, 10, 11, 12, 13, 14, 15, 16, 18, 19, 9, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 19, 10, 11, 12, 13, 14, 15, 16, 9, 17, 18, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def face3 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 12, 5, 6, 7, 8, 9, 10, 11, 13, 14, 4, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 14, 5, 6, 7, 8, 9, 10, 11, 4, 12, 13, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def face4 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 21, 22, 23, 20]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 23, 20, 21, 22]
  left_inv := by decide
  right_inv := by decide

def face5 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 4, 6, 7, 8, 5, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  invFun := ![0, 1, 2, 3, 4, 8, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def slice0 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 3, 5, 19, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 23, 20, 21, 22, 4]
  invFun := ![0, 1, 2, 3, 23, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 5, 20, 21, 22, 19]
  left_inv := by decide
  right_inv := by decide

def slice1 : Equiv.Perm (Fin 24) where
  toFun := ![0, 1, 2, 20, 4, 5, 3, 7, 8, 9, 10, 11, 12, 13, 14, 6, 16, 17, 18, 19, 15, 21, 22, 23]
  invFun := ![0, 1, 2, 6, 4, 5, 15, 7, 8, 9, 10, 11, 12, 13, 14, 20, 16, 17, 18, 19, 3, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def slice2 : Equiv.Perm (Fin 24) where
  toFun := ![14, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 18, 12, 13, 11, 15, 16, 17, 0, 19, 20, 21, 22, 23]
  invFun := ![18, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 14, 12, 13, 0, 15, 16, 17, 11, 19, 20, 21, 22, 23]
  left_inv := by decide
  right_inv := by decide

def face : Fin 6 → Equiv.Perm Label := ![face0, face1, face2, face3, face4, face5]
def slice : Fin 3 → Equiv.Perm Label := ![slice0, slice1, slice2]

def facePower (k : Fin 6 → Fin 4) : Equiv.Perm Label :=
  (List.ofFn fun i : Fin 6 => face i ^ (k i).val).prod

abbrev ControlIndex := (Fin 6 → Fin 4) × Fin 3

def control (t : ControlIndex) : Equiv.Perm Label :=
  facePower t.1 * slice t.2 * (facePower t.1)⁻¹

def finiteAtom : Alphabet → Equiv.Perm Label := Sum.elim face slice
def finiteEval : Word →* Equiv.Perm Label := FreeGroup.lift finiteAtom

def deletion : Word →* FreeGroup (Fin 6) :=
  FreeGroup.lift (Sum.elim FreeGroup.of (fun _ => 1))

def freeFacePower (k : Fin 6 → Fin 4) : Word :=
  (List.ofFn fun i : Fin 6 => FreeGroup.of (Sum.inl i : Alphabet) ^ (k i).val).prod

def freeControl (t : ControlIndex) : Word :=
  freeFacePower t.1 * FreeGroup.of (Sum.inr t.2) * (freeFacePower t.1)⁻¹

def faceMove {n : ℕ} (a : Fin n) : Fin 6 → Move n :=
  ![(0, low a, 0), (0, high a, 0), (1, low a, 0), (1, high a, 0),
    (2, low a, 0), (2, high a, 0)]
def sliceMove {n : ℕ} (a : Fin n) (i : Fin 3) : Move n := (i, a, 0)
def physicalAtom {n : ℕ} (a : Fin n) : Alphabet → Equiv.Perm (Sticker n) :=
  Sum.elim (fun i => movePermutation (faceMove a i))
    (fun i => movePermutation (sliceMove a i))
def physicalEval {n : ℕ} (a : Fin n) : Word →* Equiv.Perm (Sticker n) :=
  FreeGroup.lift (physicalAtom a)
def physicalFaceEval {n : ℕ} (a : Fin n) : FreeGroup (Fin 6) →* Equiv.Perm (Sticker n) :=
  FreeGroup.lift (fun i => movePermutation (faceMove a i))
def faceOnlyEval {n : ℕ} (a : Fin n) : Word →* Equiv.Perm (Sticker n) :=
  (physicalFaceEval a).comp deletion

def ActionBridge {n : ℕ} (a b : Fin n) : Prop :=
  ∀ t : Alphabet, ∀ i : Label,
    physicalAtom a t (lab a b i) = lab a b (finiteAtom t i)

def AllNActionBridge : Prop :=
  ∀ (n : ℕ) (a b : Fin n),
    1 ≤ a.val → 1 ≤ b.val → 2 * a.val + 2 ≤ n → 2 * b.val + 2 ≤ n →
      a ≠ b → ActionBridge a b

def cycle4 (v : Fin 4 → Label) : Equiv.Perm Label :=
  Equiv.swap (v 0) (v 1) * Equiv.swap (v 1) (v 2) * Equiv.swap (v 2) (v 3)

abbrev CertIndex := Fin 33
def certCycle : CertIndex → Fin 4 → Label :=
  ![![4, 5, 19, 23], ![4, 5, 18, 23], ![4, 5, 17, 23], ![4, 5, 9, 23], ![5, 19, 23, 14], ![5, 19, 23, 12], ![4, 5, 19, 22], ![4, 5, 19, 20], ![4, 8, 19, 23], ![7, 9, 21, 13], ![7, 17, 20, 13], ![6, 17, 21, 13], ![3, 20, 15, 6], ![3, 20, 10, 6], ![3, 20, 16, 6], ![3, 20, 11, 6], ![1, 20, 15, 6], ![2, 20, 15, 6], ![0, 20, 15, 6], ![3, 21, 15, 6], ![3, 20, 15, 5], ![1, 22, 16, 8], ![2, 22, 16, 7], ![0, 14, 15, 18], ![0, 14, 11, 9], ![1, 12, 10, 9], ![1, 12, 16, 9], ![1, 12, 11, 9], ![1, 12, 15, 9], ![2, 12, 10, 9], ![3, 12, 10, 9], ![1, 14, 10, 9], ![1, 13, 10, 9]]
def certPowers : CertIndex → Fin 6 → Fin 4 :=
  ![![0, 0, 0, 0, 0, 0], ![0, 0, 3, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![0, 0, 1, 0, 0, 0], ![0, 0, 0, 3, 0, 0], ![0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 3, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 3], ![0, 0, 1, 2, 2, 2], ![0, 0, 2, 2, 1, 2], ![0, 0, 2, 2, 2, 1], ![0, 0, 0, 0, 0, 0], ![3, 0, 0, 0, 0, 0], ![2, 0, 0, 0, 0, 0], ![1, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 3], ![2, 3, 0, 0, 2, 2], ![2, 2, 0, 0, 2, 1], ![3, 0, 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0], ![2, 2, 2, 2, 0, 0], ![1, 2, 2, 2, 0, 0], ![0, 2, 2, 2, 0, 0], ![3, 2, 2, 2, 0, 0], ![2, 1, 2, 2, 0, 0], ![2, 3, 2, 2, 0, 0], ![2, 2, 2, 0, 0, 0], ![2, 2, 2, 3, 0, 0]]
def certAxis : CertIndex → Fin 3 :=
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
def certPositive : CertIndex → Bool :=
  ![true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]

def certControlIndex (i : CertIndex) : ControlIndex := (certPowers i, certAxis i)
def certPerm (i : CertIndex) : Equiv.Perm Label := cycle4 (certCycle i)
abbrev Token := CertIndex × Bool
def tokenPerm (t : Token) : Equiv.Perm Label :=
  if t.2 then certPerm t.1 else (certPerm t.1)⁻¹
def wordEval (w : List Token) : Equiv.Perm Label := (w.map tokenPerm).prod
def path0 : List Token := [(23, true), (20, true), (0, false), (3, true)]
def path1 : List Token := [(0, true), (20, true), (7, true), (3, true)]
def pathSwap : List Token := [(0, true), (7, false), (3, true)]
def adjacentPath : Fin 23 → List Token :=
  ![[(24, true), (16, false)], [(25, true), (17, false)], [(29, true), (12, false)], [(30, true), (7, true)], [(0, true), (7, true), (3, true)], [(11, true), (10, true), (3, false)], [(22, true), (14, true), (26, false)], [(9, false), (8, true), (7, true)], [(21, false), (28, true), (12, true)], [(13, true)], [(25, false), (15, true)], [(27, false), (15, true)], [(10, true), (5, true), (3, true)], [(32, false), (31, false), (13, true)], [(12, true), (4, true), (3, true)], [(28, false), (14, true)], [(26, false), (10, false)], [(23, true), (12, true), (2, false), (3, true)], [(7, false), (1, false), (3, true)], [(0, false), (3, true)], [(19, false), (18, true), (24, true)], [(9, true), (6, false), (7, true)], [(6, true), (0, false), (7, true), (3, true)]]

def baseSwapWitness : Equiv.Perm Label :=
  let H := wordEval path1 * (wordEval path0)⁻¹
  let T := H * ((certPerm 1)⁻¹ * certPerm 0) * H⁻¹
  let B := (wordEval pathSwap)⁻¹
  B * (slice 0 * T⁻¹) * B⁻¹

def K : Subgroup (Equiv.Perm Label) := Subgroup.closure (Set.range control)

end RubikConstruction.Control
