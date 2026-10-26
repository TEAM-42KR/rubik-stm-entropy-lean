import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.NativePhaseModel
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_read_concat {n : ℕ} {X : Type*} (read : Rubik.Colouring n → X)
  (ws : List (List (RubikOBTM.BlockMove n) × Equiv.Perm X))
  (h : ∀ t∈ws, ∀ c : Rubik.Colouring n, read (RubikOBTM.applyBlockWord t.1 c)=t.2 (read c)) :
  ∀ c : Rubik.Colouring n,
  read (RubikOBTM.applyBlockWord ((ws.map Prod.fst).flatten) c) =
    ((ws.map Prod.snd).reverse.prod) (read c) := by
  have cat (u v : List (RubikOBTM.BlockMove n)) (c : Rubik.Colouring n) :
      RubikOBTM.applyBlockWord (u++v) c = RubikOBTM.applyBlockWord v (RubikOBTM.applyBlockWord u c) := by
    simp [RubikOBTM.applyBlockWord,List.foldl_append]
  revert h
  induction ws with
  | nil => intro h c; rfl
  | cons t ws ih =>
    intro h c
    have ht := h t (by simp) c
    have hs : ∀ u∈ws, ∀ c : Rubik.Colouring n,
        read (RubikOBTM.applyBlockWord u.1 c)=u.2 (read c) := by
      intro u hu c; exact h u (by simp [hu]) c
    simpa only [List.map_cons,List.flatten_cons,List.reverse_cons,List.prod_append,
      List.prod_singleton,Equiv.Perm.mul_apply,cat,ht] using
      ih hs (RubikOBTM.applyBlockWord t.1 c)

#print axioms proof_RubikOBTMCompiler_read_concat
