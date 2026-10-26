import RubikSTM.Definitions.Surface.GenericRange
import RubikSTM.Definitions.Rectangles.PayloadInterface
set_option autoImplicit false

namespace RubikGlobalWord
open Rubik RubikGlobal

def advance {n : ℕ} (c : Position n) (w : List (Move n)) : Position n :=
  ⟨applyWord w c.val, by
    obtain ⟨u,hu⟩ := c.property
    refine ⟨u++w, ?_⟩
    simp only [applyWord, List.foldl_append]
    change applyWord w (applyWord u (solved n)) = _
    rw [hu]
    rfl⟩

def Recolour {n : ℕ} (S : Set (Sticker n)) (c d : Colouring n)
    (w : List (Move n)) : Prop :=
  (∀ s ∈ S, applyWord w c s = d s) ∧
    (∀ s ∉ S, applyWord w c s = c s)

def Nongeneric {n : ℕ} (s : Sticker n) : Prop :=
  RubikCore.IsCore s ∨ ∃ e : ExceptionalIndex n, s ∈ ExceptionalRange e

abbrev GroupPair (h : ℕ) := {p : Fin h × Fin h // p.1 < p.2}

def groupIndices {n h : ℕ} (f : I n → Fin h) (r : Fin h) : Finset (I n) :=
  Finset.univ.filter (fun i => f i = r)

def depthGroup {n h : ℕ} (f : I n → Fin h) (r : Fin h) : Finset (Fin n) :=
  (groupIndices f r).image depth

abbrev SamePair {n h : ℕ} (f : I n → Fin h) :=
  {p : Q n // f p.val.1 = f p.val.2}

abbrev Task {n h : ℕ} (f : I n → Fin h) := GroupPair h ⊕ SamePair f

def taskOf {n h : ℕ} (f : I n → Fin h) (p : Q n) : Task f :=
  if hp : f p.val.1 < f p.val.2 then Sum.inl ⟨(f p.val.1,f p.val.2),hp⟩
  else if hq : f p.val.2 < f p.val.1 then Sum.inl ⟨(f p.val.2,f p.val.1),hq⟩
  else Sum.inr ⟨p,le_antisymm (le_of_not_gt hq) (le_of_not_gt hp)⟩

def Region {n h : ℕ} (f : I n → Fin h) (t : Task f) : Set (Sticker n) :=
  {s | ∃ p : Q n, taskOf f p = t ∧ s ∈ GenericRange p}

def sameCount {n h : ℕ} (f : I n → Fin h) : ℕ := Fintype.card (SamePair f)

def rectangleCost {n h : ℕ} (C : ℕ) (f : I n → Fin h)
    (k M : GroupPair h → ℕ) (L : ℕ) (p : GroupPair h) : ℕ :=
  L * (RubikRectangle.rowCeil (depthGroup f p.val.1).card (k p) + 3) *
    ((depthGroup f p.val.2).card + C * (k p + 1) * M p)

def balancedColour {n h : ℕ} (hh : 0 < h) (i : I n) : Fin h :=
  ⟨i.val % h, Nat.mod_lt _ hh⟩

end RubikGlobalWord
