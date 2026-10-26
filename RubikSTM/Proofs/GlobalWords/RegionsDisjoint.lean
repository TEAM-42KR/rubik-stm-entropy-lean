import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
import RubikSTM.Definitions.Core.CoreAction
import RubikSTM.Lemmas.Surface.GenericRangesDisjoint
set_option autoImplicit false

theorem proof_RubikGlobalWord_regions_disjoint {n h : ℕ} (f : RubikGlobal.I n → Fin h) (t u : RubikGlobalWord.Task f)
  (hne : t ≠ u) : Disjoint (RubikGlobalWord.Region f t) (RubikGlobalWord.Region f u) := by
  apply Set.disjoint_left.mpr
  rintro s ⟨p,hp,hsp⟩ ⟨q,hq,hsq⟩
  have he : p=q := by
    by_contra hn
    exact Set.disjoint_left.mp (RubikGlobal.generic_ranges_disjoint p q hn) hsp hsq
  subst q
  exact hne (hp.symm.trans hq)

#print axioms proof_RubikGlobalWord_regions_disjoint
