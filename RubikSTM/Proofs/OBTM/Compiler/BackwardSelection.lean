import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.UniversalOwnProfile
import RubikSTM.Lemmas.OBTM.Compiler.SuffixConsZero
import RubikSTM.Lemmas.OBTM.Compiler.SuffixConsSucc
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_backward_selection {L s : ℕ} {K : Fin L → Type*} [∀ i, CommGroup (K i)] {X : Type*}
  (act : (i : Fin L) → K i → Equiv.Perm X) (A : (i : Fin L) → Finset (K i))
  (hA : RubikOBTMCompiler.UniversalOwnProfile act A) (x y : Fin s → X) :
  ∃ w : Fin s → RubikOBTMCompiler.Profile L K, (∀ d i, w d i ∈ A i) ∧
    ∀ b : Fin s, RubikOBTMCompiler.phasePerm act (fun i => RubikOBTMCompiler.suffix w b.val i) (x b) = y b := by
  induction s with
  | zero =>
    refine ⟨Fin.elim0, ?_, ?_⟩
    · intro d; exact Fin.elim0 d
    · intro b; exact Fin.elim0 b
  | succ s ih =>
    obtain ⟨v,hv,hend⟩ := ih (fun d => x d.succ) (fun d => y d.succ)
    obtain ⟨u,hu,h0⟩ := hA (x 0) (y 0) (fun i => RubikOBTMCompiler.suffix v 0 i)
    refine ⟨Fin.cons u v, ?_, ?_⟩
    · intro d
      refine Fin.cases ?_ ?_ d
      · simpa using hu
      · intro d; simpa using hv d
    · intro b
      refine Fin.cases ?_ ?_ b
      · have he : (fun i => RubikOBTMCompiler.suffix (Fin.cons u v) 0 i) =
            (fun i => RubikOBTMCompiler.suffix v 0 i * u i) := by
          funext i
          rw [RubikOBTMCompiler.suffix_cons_zero,mul_comm]
        simpa only [Fin.val_zero,Fin.cons_zero,he] using h0
      · intro b
        simpa only [Fin.val_succ,RubikOBTMCompiler.suffix_cons_succ] using hend b

#print axioms proof_RubikOBTMCompiler_backward_selection
