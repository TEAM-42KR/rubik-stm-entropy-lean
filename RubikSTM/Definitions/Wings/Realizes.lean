import RubikSTM.Definitions.Wings.Embed
set_option autoImplicit false
open Rubik RubikWing
set_option linter.unusedSimpArgs false

 theorem RubikWing.level_injective {n : ℕ} {c : Fin n} (hc : Admissible n c) :
    Function.Injective (level c) := by
  have hl := hc.one_le
  have hs := hc.small
  have hn := c.isLt
  have d01 : lo c ≠ c := by intro h; have h' := congrArg Fin.val h; simp [lo] at h'; omega
  have d02 : lo c ≠ c.rev := by intro h; have h' := congrArg Fin.val h; simp [lo, Fin.rev] at h'; omega
  have d03 : lo c ≠ hi c := by intro h; have h' := congrArg Fin.val h; simp [lo, hi] at h'; omega
  have d12 : c ≠ c.rev := by intro h; have h' := congrArg Fin.val h; simp [Fin.rev] at h'; omega
  have d13 : c ≠ hi c := by intro h; have h' := congrArg Fin.val h; simp [hi] at h'; omega
  have d23 : c.rev ≠ hi c := by intro h; have h' := congrArg Fin.val h; simp [hi, Fin.rev] at h'; omega
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all only [level, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue,
      d01, Ne.symm d01, d02, Ne.symm d02, d03, Ne.symm d03,
      d12, Ne.symm d12, d13, Ne.symm d13, d23, Ne.symm d23]

 theorem RubikWing.level_rev {n : ℕ} (c : Fin n) (k : Fin 4) :
    level c k.rev = (level c k).rev := by
  have hn := c.isLt
  fin_cases k <;> apply Fin.ext <;> simp [level, lo, hi, Fin.rev] <;> omega

 theorem RubikWing.embed_rotation {n : ℕ} (c : Fin n) (a : Axis) (s : Sticker 4) :
    surfaceRotation n a (embed c s) = embed c (surfaceRotation 4 a s) := by
  apply Subtype.ext
  rcases s with ⟨⟨⟨x,y,z⟩, b⟩,hs⟩
  fin_cases a <;>
    simp [surfaceRotation, rawRotation, coordinateRotation, embed, embedPos,
      normalRotation, level_rev]

 theorem RubikWing.embed_quarter {n : ℕ} {c : Fin n} (hc : Admissible n c)
    (a : Axis) (k : Fin 4) (s : Sticker 4) :
    sliceQuarter n a (level c k) (embed c s) = embed c (sliceQuarter 4 a k s) := by
  have hcoord : coordinate (embedPos c s.val.1) a = level c (coordinate s.val.1 a) := by
    fin_cases a <;> rfl
  have hlevel := level_injective hc
  by_cases h : coordinate s.val.1 a = k
  · have hh : coordinate (embed c s).val.1 a = level c k := by
      change coordinate (embedPos c s.val.1) a = level c k
      rw [hcoord, h]
    simpa [sliceQuarter, h, hh] using embed_rotation c a s
  · have hh : coordinate (embed c s).val.1 a ≠ level c k := by
      change coordinate (embedPos c s.val.1) a ≠ level c k
      rw [hcoord]
      exact fun he => h (hlevel he)
    simp [sliceQuarter, h, hh]

 theorem RubikWing.embed_lab {n : ℕ} (c : Fin n) (i : Label) (b : Side) :
    embed c (lab (1 : Fin 4) i b) = lab c i b := by
  fin_cases i <;> fin_cases b <;> apply Subtype.ext <;> rfl

open Rubik RubikWing
set_option maxRecDepth 2048
set_option maxHeartbeats 1500000

theorem RubikWing.reference_atom_lab (t : Alphabet) (i : Label) (b : Side) :
    physicalAtom (1 : Fin 4) t (lab 1 i b) = lab 1 (finiteAtom t i) b := by
  cases t with
  | inl f => fin_cases f <;> fin_cases i <;> fin_cases b <;> decide
  | inr f => fin_cases f <;> fin_cases i <;> fin_cases b <;> decide

theorem RubikWing.atom_embed {n : ℕ} {c : Fin n} (hc : Admissible n c) (t : Alphabet) (s : Sticker 4) :
    physicalAtom c t (embed c s) = embed c (physicalAtom (1 : Fin 4) t s) := by
  cases t with
  | inl f =>
    fin_cases f
    · simpa [physicalAtom, faceMove, sliceMove, movePermutation, level, lo, hi] using
        (embed_quarter hc (0 : Axis) (0 : Fin 4) s)
    · simpa [physicalAtom, faceMove, sliceMove, movePermutation, level, lo, hi] using
        (embed_quarter hc (0 : Axis) (3 : Fin 4) s)
    · simpa [physicalAtom, faceMove, sliceMove, movePermutation, level, lo, hi] using
        (embed_quarter hc (1 : Axis) (0 : Fin 4) s)
    · simpa [physicalAtom, faceMove, sliceMove, movePermutation, level, lo, hi] using
        (embed_quarter hc (1 : Axis) (3 : Fin 4) s)
    · simpa [physicalAtom, faceMove, sliceMove, movePermutation, level, lo, hi] using
        (embed_quarter hc (2 : Axis) (0 : Fin 4) s)
    · simpa [physicalAtom, faceMove, sliceMove, movePermutation, level, lo, hi] using
        (embed_quarter hc (2 : Axis) (3 : Fin 4) s)
  | inr f =>
    fin_cases f
    · simpa [physicalAtom, faceMove, sliceMove, movePermutation, level, lo, hi] using
        (embed_quarter hc (0 : Axis) (1 : Fin 4) s)
    · simpa [physicalAtom, faceMove, sliceMove, movePermutation, level, lo, hi] using
        (embed_quarter hc (0 : Axis) (2 : Fin 4) s)
    · simpa [physicalAtom, faceMove, sliceMove, movePermutation, level, lo, hi] using
        (embed_quarter hc (1 : Axis) (1 : Fin 4) s)
    · simpa [physicalAtom, faceMove, sliceMove, movePermutation, level, lo, hi] using
        (embed_quarter hc (1 : Axis) (2 : Fin 4) s)
    · simpa [physicalAtom, faceMove, sliceMove, movePermutation, level, lo, hi] using
        (embed_quarter hc (2 : Axis) (1 : Fin 4) s)
    · simpa [physicalAtom, faceMove, sliceMove, movePermutation, level, lo, hi] using
        (embed_quarter hc (2 : Axis) (2 : Fin 4) s)

theorem RubikWing.physical_atom_lab {n : ℕ} {c : Fin n} (hc : Admissible n c)
    (t : Alphabet) (i : Label) (b : Side) :
    physicalAtom c t (lab c i b) = lab c (finiteAtom t i) b := by
  calc
    physicalAtom c t (lab c i b) = physicalAtom c t (embed c (lab (1 : Fin 4) i b)) :=
      congrArg (physicalAtom c t) (embed_lab c i b).symm
    _ = embed c (physicalAtom (1 : Fin 4) t (lab 1 i b)) := atom_embed hc t _
    _ = embed c (lab (1 : Fin 4) (finiteAtom t i) b) := congrArg (embed c) (reference_atom_lab t i b)
    _ = lab c (finiteAtom t i) b := embed_lab c _ b

namespace RubikWing

def Realizes {n : ℕ} (c : Fin n) (σ : Equiv.Perm Label) (w : Word) : Prop :=
  deletion w = 1 ∧ ∀ i b, physicalEval c w (lab c i b) = lab c (σ i) b
end RubikWing
