import Mathlib
set_option autoImplicit false

namespace RubikGrouping

def groupOf (m h : ℕ) (hh : 0 < h) (i : Fin m) : Fin h :=
  ⟨i.val % h, Nat.mod_lt _ hh⟩

def group (m h : ℕ) (hh : 0 < h) (t : Fin h) : Finset (Fin m) :=
  Finset.univ.filter (fun i => groupOf m h hh i = t)

def sameGroupPairs (m h : ℕ) (hh : 0 < h) : Finset (Fin m × Fin m) :=
  Finset.univ.filter (fun p => p.1 ≠ p.2 ∧
    groupOf m h hh p.1 = groupOf m h hh p.2)

def crossGroupProducts (m h : ℕ) (hh : 0 < h) : ℝ :=
  ∑ s : Fin h, ∑ t ∈ Finset.univ.filter (fun t : Fin h => s < t),
    ((group m h hh s).card : ℝ) * ((group m h hh t).card : ℝ)

end RubikGrouping
