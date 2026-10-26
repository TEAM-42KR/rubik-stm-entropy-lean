import Mathlib
import RubikSTM.Definitions.Grouping.GroupOf
import RubikSTM.Definitions.GlobalWords.Region
set_option autoImplicit false

namespace RubikOBTM.Grouping

noncomputable def sortIndex (m h : ℕ) (hh : 0 < h) : Equiv.Perm (Fin m) :=
  Tuple.sort (RubikGrouping.groupOf m h hh)

noncomputable def groupOf (m h : ℕ) (hh : 0 < h) (i : Fin m) : Fin h :=
  RubikGrouping.groupOf m h hh (sortIndex m h hh i)

noncomputable def group (m h : ℕ) (hh : 0 < h) (t : Fin h) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => groupOf m h hh i = t)

noncomputable def sameGroupPairs (m h : ℕ) (hh : 0 < h) : Finset (Fin m × Fin m) := by
  classical
  exact Finset.univ.filter (fun p => p.1 ≠ p.2 ∧ groupOf m h hh p.1 = groupOf m h hh p.2)

noncomputable def crossGroupProducts (m h : ℕ) (hh : 0 < h) : ℝ :=
  ∑ s : Fin h, ∑ t ∈ Finset.univ.filter (fun t : Fin h => s < t),
    ((group m h hh s).card : ℝ) * ((group m h hh t).card : ℝ)

noncomputable def positiveGroup (m h : ℕ) (hh : 0 < h) (t : Fin h) : Finset ℕ :=
  (group m h hh t).image (fun i => i.val + 1)

noncomputable def lower (m h : ℕ) (hh : 0 < h) (t : Fin h)
    (hg : (group m h hh t).Nonempty) : ℕ :=
  ((group m h hh t).min' hg).val + 1

noncomputable def upper (m h : ℕ) (hh : 0 < h) (t : Fin h)
    (hg : (group m h hh t).Nonempty) : ℕ :=
  ((group m h hh t).max' hg).val + 1

noncomputable def depthGroup (n h : ℕ) (hh : 0 < h) (t : Fin h) : Finset (Fin n) :=
  (group ((n - 2) / 2) h hh t).image RubikGlobal.depth

end RubikOBTM.Grouping
