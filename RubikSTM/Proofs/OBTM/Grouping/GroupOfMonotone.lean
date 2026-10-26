import RubikSTM.Definitions.OBTM.Grouping.GroupOf
set_option autoImplicit false

theorem proof_RubikOBTM_Grouping_groupOf_monotone (m h : ℕ) (hh : 0 < h) : Monotone (RubikOBTM.Grouping.groupOf m h hh) := by
  exact Tuple.monotone_sort (RubikGrouping.groupOf m h hh)
