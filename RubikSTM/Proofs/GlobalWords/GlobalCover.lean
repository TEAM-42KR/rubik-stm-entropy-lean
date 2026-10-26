import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
import RubikSTM.Definitions.Core.CoreAction
import RubikSTM.Lemmas.Surface.SurfaceCover
set_option autoImplicit false

theorem proof_RubikGlobalWord_global_cover {n h : ℕ} (f : RubikGlobal.I n → Fin h) (s : Rubik.Sticker n) :
  RubikGlobalWord.Nongeneric s ∨ ∃ t : RubikGlobalWord.Task f, s ∈ RubikGlobalWord.Region f t := by
  rcases RubikGlobal.surface_cover s with hc | hw | hd | hx | hg
  · exact Or.inl (Or.inl hc)
  · obtain ⟨i,hi⟩ := hw
    exact Or.inl (Or.inr ⟨(i,0), by simpa [RubikGlobal.ExceptionalRange] using hi⟩)
  · obtain ⟨i,hi⟩ := hd
    exact Or.inl (Or.inr ⟨(i,1), by simpa [RubikGlobal.ExceptionalRange] using hi⟩)
  · obtain ⟨i,hi⟩ := hx
    exact Or.inl (Or.inr ⟨(i,2), by simpa [RubikGlobal.ExceptionalRange] using hi⟩)
  · obtain ⟨p,hp⟩ := hg
    exact Or.inr ⟨RubikGlobalWord.taskOf f p,p,rfl,hp⟩

#print axioms proof_RubikGlobalWord_global_cover
