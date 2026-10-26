import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.UniversalOwnProfile
import RubikSTM.Lemmas.OBTM.Compiler.BackwardSelection
import RubikSTM.Lemmas.OBTM.Compiler.SuffixProduct
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_ordered_backward_selection {I : Type*} [LinearOrder I] {L : ℕ}
  {K : Fin L → Type*} [∀ i, CommGroup (K i)] {X : Type*}
  (Y : Finset I) (act : (i : Fin L) → K i → Equiv.Perm X)
  (A : (i : Fin L) → Finset (K i)) (hA : RubikOBTMCompiler.UniversalOwnProfile act A)
  (x y : Y → X) :
  ∃ w : I → RubikOBTMCompiler.Profile L K, (∀ b∈Y, ∀ i, w b i∈A i) ∧
    ∀ b : Y, RubikOBTMCompiler.phasePerm act (fun i => ∏ d∈Y.filter (fun d => b.val ≤ d), w d i)
      (x b) = y b := by
  classical
  let e := Y.orderIsoOfFin rfl
  obtain ⟨v,hv,hend⟩ := RubikOBTMCompiler.backward_selection act A hA (fun b => x (e b)) (fun b => y (e b))
  let w (b : I) : RubikOBTMCompiler.Profile L K := if hb : b∈Y then v (e.symm ⟨b,hb⟩) else 1
  refine ⟨w,?_,?_⟩
  · intro b hb i
    simpa only [w,dif_pos hb] using hv (e.symm ⟨b,hb⟩) i
  · intro b
    have hf (i : Fin L) :
        (∏ d∈(Finset.univ.filter (fun d : Fin Y.card => (e.symm b).val ≤ d.val)), v d i) =
          ∏ d∈Y.filter (fun d => b.val ≤ d), w d i := by
      apply Finset.prod_bij (fun d _ => (e d).val)
      · intro d hd
        apply Finset.mem_filter.mpr
        refine ⟨(e d).property,?_⟩
        have hh : e.symm b ≤ d := (Finset.mem_filter.mp hd).2
        change b ≤ e d
        simpa only [e.apply_symm_apply] using e.monotone hh
      · intro d hd z hz he
        exact e.injective (Subtype.ext he)
      · intro d hd
        have hy : d∈Y := (Finset.mem_filter.mp hd).1
        refine ⟨e.symm ⟨d,hy⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
        · exact show e.symm b ≤ e.symm ⟨d,hy⟩ from e.symm.monotone (Finset.mem_filter.mp hd).2
        · exact congrArg Subtype.val (e.apply_symm_apply ⟨d,hy⟩)
      · intro d hd
        simp only [w,dif_pos (e d).property,e.symm_apply_apply]
    have hp : (fun i => ∏ d∈Y.filter (fun d => b.val ≤ d), w d i) =
        (fun i => RubikOBTMCompiler.suffix v (e.symm b).val i) := by
      funext i
      rw [← hf]
      exact (RubikOBTMCompiler.suffix_product (fun d => v d i) (e.symm b).val).symm
    rw [hp]
    simpa only [e.apply_symm_apply] using hend (e.symm b)

#print axioms proof_RubikOBTMCompiler_ordered_backward_selection
