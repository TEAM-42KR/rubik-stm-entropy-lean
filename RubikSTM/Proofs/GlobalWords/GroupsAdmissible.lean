import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
import RubikSTM.Definitions.Core.CoreAction
set_option autoImplicit false

theorem proof_RubikGlobalWord_groups_admissible {n h : ℕ} (f : RubikGlobal.I n → Fin h) (r : RubikGlobalWord.GroupPair h) :
  RubikPayload.Admissible (RubikGlobalWord.depthGroup f r.val.1)
    (RubikGlobalWord.depthGroup f r.val.2) := by
  have depthinj : Function.Injective (RubikGlobal.depth (n:=n)) := by
    intro i j he
    apply Fin.ext
    have hh := congrArg Fin.val he
    change i.val+1=j.val+1 at hh
    omega
  have H (r : Fin h) : ∀ a ∈ RubikGlobalWord.depthGroup f r, RubikPayload.Half a := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    have hb := i.isLt
    constructor <;> change _ ≤ _ <;> simp only [RubikGlobal.depth] <;> omega
  refine ⟨H _,H _,?_⟩
  apply Finset.disjoint_left.mpr
  intro a ha hb
  obtain ⟨i,hi,hei⟩ := Finset.mem_image.mp ha
  obtain ⟨j,hj,hej⟩ := Finset.mem_image.mp hb
  have he : i=j := depthinj (hei.trans hej.symm)
  subst j
  have H₁ := (Finset.mem_filter.mp hi).2
  have H₂ := (Finset.mem_filter.mp hj).2
  have := r.property
  rw [← H₁,← H₂] at this
  exact lt_irrefl _ this

#print axioms proof_RubikGlobalWord_groups_admissible
