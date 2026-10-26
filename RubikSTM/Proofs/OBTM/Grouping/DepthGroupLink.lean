import RubikSTM.Definitions.OBTM.Grouping.GroupOf
import RubikSTM.Lemmas.OBTM.Grouping.GroupCardEq
set_option autoImplicit false

theorem proof_RubikOBTM_Grouping_depthGroup_link (n h : ℕ) (hh : 0 < h) (t : Fin h) :
    RubikOBTM.Grouping.depthGroup n h hh t =
      RubikGlobalWord.depthGroup (RubikOBTM.Grouping.groupOf ((n-2)/2) h hh) t ∧
    (RubikOBTM.Grouping.depthGroup n h hh t).card = (RubikGrouping.group ((n-2)/2) h hh t).card := by
  have hinj : Function.Injective (RubikGlobal.depth (n:=n)) := by
    intro i j he
    apply Fin.ext
    have hv := congrArg Fin.val he
    change i.val + 1 = j.val + 1 at hv
    omega
  refine ⟨rfl, ?_⟩
  rw [RubikOBTM.Grouping.depthGroup, Finset.card_image_of_injective _ hinj,
    RubikOBTM.Grouping.group_card_eq]
