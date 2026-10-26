import RubikSTM.Definitions.OBTM.Grouping.GroupOf
import RubikSTM.Lemmas.OBTM.Grouping.FibreInterval
set_option autoImplicit false

theorem proof_RubikOBTM_Grouping_depthGroup_interval (n h : ℕ) (hh : 0 < h) (t : Fin h)
    (hg : (RubikOBTM.Grouping.group ((n-2)/2) h hh t).Nonempty) :
    RubikOBTM.Grouping.depthGroup n h hh t = Finset.univ.filter (fun d : Fin n =>
      RubikOBTM.Grouping.lower ((n-2)/2) h hh t hg ≤ d.val ∧
      d.val ≤ RubikOBTM.Grouping.upper ((n-2)/2) h hh t hg) ∧
    1 ≤ RubikOBTM.Grouping.lower ((n-2)/2) h hh t hg ∧
    RubikOBTM.Grouping.lower ((n-2)/2) h hh t hg ≤ RubikOBTM.Grouping.upper ((n-2)/2) h hh t hg ∧
    2 * RubikOBTM.Grouping.upper ((n-2)/2) h hh t hg + 2 ≤ n := by
  classical
  obtain ⟨heq, hL, hLU, hU⟩ := RubikOBTM.Grouping.fibre_interval ((n-2)/2) h hh t hg
  have hm : 0 < (n-2)/2 := by
    obtain ⟨i, hi⟩ := hg
    have := i.isLt
    omega
  refine ⟨?_, hL, hLU, by omega⟩
  ext d
  have hd : d ∈ RubikOBTM.Grouping.depthGroup n h hh t ↔
      d.val ∈ RubikOBTM.Grouping.positiveGroup ((n-2)/2) h hh t := by
    constructor
    · intro hd
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hd
      exact Finset.mem_image.mpr ⟨i, hi, congrArg Fin.val he⟩
    · intro hd
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hd
      exact Finset.mem_image.mpr ⟨i, hi, Fin.ext he⟩
  rw [hd, heq]
  simp only [Finset.mem_Icc, Finset.mem_filter, Finset.mem_univ, true_and]
