import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
import RubikSTM.Definitions.Core.CoreAction
import RubikSTM.Lemmas.LocalActions.Generic.UniformReachableRecolour
set_option autoImplicit false

theorem proof_RubikGlobalWord_generic_local_recolour : ∃ C : ℕ, ∀ (n : ℕ) (p : RubikGlobal.Q n) (c d : Rubik.Position n),
  ∃ w : List (Rubik.Move n), w.length ≤ C ∧
    RubikGlobalWord.Recolour (RubikGlobal.GenericRange p) c.val d.val w := by
  obtain ⟨C,hC⟩ := RubikLocal.Generic.uniform_reachable_recolour
  refine ⟨C,?_⟩
  intro n p c d
  have hp := p.property
  have hi := p.val.1.isLt
  have hj := p.val.2.isLt
  have hg : RubikGeometry.Generic n (RubikGlobal.depth p.val.1) (RubikGlobal.depth p.val.2) := by
    constructor
    all_goals first | (change _ ≤ _; simp only [RubikGlobal.depth]; omega) |
      (intro he; have H := congrArg Fin.val he; apply hp; apply Fin.ext; change _+1=_+1 at H; omega)
  obtain ⟨w,hw,hm,hp,hf⟩ := hC n _ _ hg c.val d.val c.property d.property
  refine ⟨w,hw,?_,?_⟩
  · rintro s ⟨i,rfl⟩
    exact hm i
  · exact hf

#print axioms proof_RubikGlobalWord_generic_local_recolour
