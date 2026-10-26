import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.VectorAction
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_lifted_book_cover {T k L : ℕ} {Z : Type*} (hT : 0 < T)
  (K : Fin T → Type*) [∀ p, Group (K p)] (C : ∀ p, Finset (K p))
  (act : ∀ p, K p →* Equiv.Perm Z) (B : RubikOBTM.Periodic.Book hT K C k L)
  (hB : RubikOBTM.Periodic.CoversAll hT K C act B) :
  RubikOBTMCompiler.UniversalOwnProfile
    (fun i : Fin L => (RubikOBTMCompiler.vectorAction (k:=k) (act (RubikOBTM.Periodic.phase T hT i))))
    (RubikOBTMCompiler.liftedBook hT K C B) := by
  classical
  intro x y n
  obtain ⟨w,hw,hend⟩ := hB x y n
  refine ⟨(fun i z => (w i z).val),?_,?_⟩
  · intro i
    exact Finset.mem_image.mpr ⟨w i,hw i,rfl⟩
  · have hfold (ps : List (Equiv.Perm (Fin k → Z))) (v : Fin k → Z) :
        ps.reverse.prod v = ps.foldl (fun v p => p v) v := by
      induction ps generalizing v with
      | nil => rfl
      | cons p ps ih =>
        simpa only [List.reverse_cons,List.prod_append,List.prod_singleton,
          Equiv.Perm.mul_apply,List.foldl_cons] using ih (p v)
    have hcoord (ps : List (Fin k → Equiv.Perm Z)) (v : Fin k → Z) :
        (ps.map RubikOBTMCompiler.coordinatePerm).foldl (fun v p => p v) v =
          fun z => (ps.map (fun p => p z)).foldl (fun v p => p v) (v z) := by
      induction ps generalizing v with
      | nil => rfl
      | cons p ps ih =>
        simp only [List.map_cons,List.foldl_cons]
        rw [ih]
        rfl
    let ps : List (Fin k → Equiv.Perm Z) := List.ofFn (fun i : Fin L =>
      fun z => act (RubikOBTM.Periodic.phase T hT i) (n i z * (w i z).val))
    have he : List.ofFn (fun i : Fin L =>
        RubikOBTMCompiler.vectorAction (k:=k) (act (RubikOBTM.Periodic.phase T hT i))
          (n i * (fun z => (w i z).val))) = ps.map RubikOBTMCompiler.coordinatePerm := by
      simp only [ps,List.map_ofFn]
      rfl
    change (List.ofFn (fun i : Fin L =>
        RubikOBTMCompiler.vectorAction (k:=k) (act (RubikOBTM.Periodic.phase T hT i))
          (n i * (fun z => (w i z).val)))).reverse.prod x = y
    rw [he,hfold,hcoord]
    unfold RubikOBTM.Periodic.eval at hend
    simpa only [ps,List.map_ofFn,Function.comp_def] using hend

#print axioms proof_RubikOBTMCompiler_lifted_book_cover
