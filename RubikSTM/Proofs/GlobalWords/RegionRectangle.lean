import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
import RubikSTM.Definitions.Core.CoreAction
import RubikSTM.Lemmas.GlobalWords.TaskPairIff
set_option autoImplicit false

theorem proof_RubikGlobalWord_region_rectangle {n h : ℕ} (f : RubikGlobal.I n → Fin h) (r : RubikGlobalWord.GroupPair h) :
  RubikGlobalWord.Region f (Sum.inl r) =
    {s | RubikPayload.Rectangles (RubikGlobalWord.depthGroup f r.val.1)
      (RubikGlobalWord.depthGroup f r.val.2) s} := by
  ext s
  constructor
  · rintro ⟨p,hp,⟨i,hi⟩⟩
    have hd (j : RubikGlobal.I n) : RubikGlobal.depth j ∈ RubikGlobalWord.depthGroup f (f j) := by
      exact Finset.mem_image.mpr ⟨j,by simp [RubikGlobalWord.groupIndices],rfl⟩
    rcases (RubikGlobalWord.task_pair_iff f p r).mp hp with H | H
    · refine ⟨RubikGlobal.depth p.val.1, ?_, RubikGlobal.depth p.val.2, ?_, Or.inl ⟨i,hi⟩⟩
      · rw [← H.1]; exact hd _
      · rw [← H.2]; exact hd _
    · refine ⟨RubikGlobal.depth p.val.2, ?_, RubikGlobal.depth p.val.1, ?_, Or.inr ⟨i,hi⟩⟩
      · rw [← H.1]; exact hd _
      · rw [← H.2]; exact hd _
  · rintro ⟨a,ha,b,hb,hs⟩
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hb
    have hfu : f u = r.val.1 := (Finset.mem_filter.mp hu).2
    have hfv : f v = r.val.2 := (Finset.mem_filter.mp hv).2
    have huv : u ≠ v := by intro he; subst v; have := r.property; rw [← hfu,← hfv] at this; exact (lt_irrefl _ this)
    rcases hs with ⟨i,hi⟩ | ⟨i,hi⟩
    · let p : RubikGlobal.Q n := ⟨(u,v),huv⟩
      exact ⟨p,(RubikGlobalWord.task_pair_iff f p r).mpr (Or.inl ⟨hfu,hfv⟩),i,hi⟩
    · let p : RubikGlobal.Q n := ⟨(v,u),Ne.symm huv⟩
      exact ⟨p,(RubikGlobalWord.task_pair_iff f p r).mpr (Or.inr ⟨hfu,hfv⟩),i,hi⟩

#print axioms proof_RubikGlobalWord_region_rectangle
