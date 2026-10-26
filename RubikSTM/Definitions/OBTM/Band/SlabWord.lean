import RubikSTM.Definitions.OBTM.Band.CleanAction
set_option autoImplicit false

namespace RubikOBTM.Band
open Rubik

def actualSlabPlus : Perm := Equiv.swap 2 4 * Equiv.swap 4 15 * Equiv.swap 15 17

def actualSlabMinus : Perm := Equiv.swap 3 13 * Equiv.swap 13 16 * Equiv.swap 16 19

def refRelabel : Perm where
  toFun := ![15, 11, 10, 16, 19, 5, 23, 4, 9, 20, 8, 14, 18, 6, 22, 12, 17, 21, 7, 13, 3, 1, 0, 2]
  invFun := ![22, 21, 23, 20, 7, 5, 13, 18, 10, 8, 2, 1, 15, 19, 11, 0, 3, 16, 12, 4, 9, 17, 14, 6]
  left_inv := by decide
  right_inv := by decide

def refPosTable {n : ℕ} (a d : Fin n) : Fin 24 → Coord n :=
  ![(RubikConstruction.Control.low a, a, d.rev),
    (RubikConstruction.Control.low a, d, a),
    (RubikConstruction.Control.low a, d.rev, a.rev),
    (RubikConstruction.Control.low a, a.rev, d),
    (a, RubikConstruction.Control.low a, d),
    (a, d, RubikConstruction.Control.high a),
    (a, d.rev, RubikConstruction.Control.low a),
    (a, RubikConstruction.Control.high a, d.rev),
    (d, RubikConstruction.Control.low a, a.rev),
    (d, a, RubikConstruction.Control.low a),
    (d, a.rev, RubikConstruction.Control.high a),
    (d, RubikConstruction.Control.high a, a),
    (d.rev, RubikConstruction.Control.low a, a),
    (d.rev, a, RubikConstruction.Control.high a),
    (d.rev, a.rev, RubikConstruction.Control.low a),
    (d.rev, RubikConstruction.Control.high a, a.rev),
    (a.rev, RubikConstruction.Control.low a, d.rev),
    (a.rev, d, RubikConstruction.Control.low a),
    (a.rev, d.rev, RubikConstruction.Control.high a),
    (a.rev, RubikConstruction.Control.high a, d),
    (RubikConstruction.Control.high a, a, d),
    (RubikConstruction.Control.high a, d, a.rev),
    (RubikConstruction.Control.high a, d.rev, a),
    (RubikConstruction.Control.high a, a.rev, d.rev)]
def refNormalTable : Fin 24 → Normal :=
  ![(0, false), (0, false), (0, false), (0, false), (1, false), (2, true), (2, false), (1, true), (1, false), (2, false), (2, true), (1, true), (1, false), (2, true), (2, false), (1, true), (1, false), (2, false), (2, true), (1, true), (0, true), (0, true), (0, true), (0, true)]
def refLab {n : ℕ} (a d : Fin n) (i : Fin 24) : Sticker n :=
  ⟨(refPosTable a d i, refNormalTable i), by
    fin_cases i <;> simp [refPosTable, refNormalTable, IsSurface, coordinate,
      RubikConstruction.Control.low, RubikConstruction.Control.high]⟩

def slabDepths {n : ℕ} (u v : Fin n) : Finset (Fin n) :=
  (Finset.Icc u v).image Fin.rev

def slabPerm {n : ℕ} (u v : Fin n) : Equiv.Perm (Sticker n) :=
  RubikBand.parallelBaseline 2 (slabDepths u v)

def slabWord {n : ℕ} (a u v : Fin n) (h : Admissible n a u v) :
    List (RubikOBTM.BlockMove n) :=
  [(2,true,⟨v.val, by have := h.upper_small; omega⟩,0),
   (2,true,⟨u.val-1, by have hu := h.lower_pos; have ho := h.ordered; have hv := h.upper_small; omega⟩,2)]

end RubikOBTM.Band
