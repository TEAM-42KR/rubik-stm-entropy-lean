import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
import RubikSTM.Definitions.Core.CoreAction
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open Rubik RubikGlobal RubikGlobalWord
theorem proof_RubikGlobalWord_Exceptional_finite_cleanup {n : ℕ} {E : Type*} [Fintype E]
    (P : Set (Sticker n)) (R : E → Set (Sticker n)) (C : ℕ)
    (hR : ∀ e, R e ⊆ P)
    (hstep : ∀ (e : E) (c : Position n), ∃ w : List (Move n), w.length ≤ C ∧
      (∀ s ∈ R e, applyWord w c.val s = solved n s) ∧
      (∀ s ∈ P, c.val s = solved n s → applyWord w c.val s = solved n s))
    (c : Position n) : ∃ w : List (Move n), w.length ≤ C * Fintype.card E ∧
      ∀ s, ((s ∈ P ∧ c.val s = solved n s) ∨ ∃ e, s ∈ R e) →
        applyWord w c.val s = solved n s := by
  classical
  have happ (u v : List (Move n)) (d : Colouring n) :
      applyWord (u ++ v) d = applyWord v (applyWord u d) := by
    simp only [applyWord, List.foldl_append]
  have sweep (es : List E) : ∀ d : Position n,
      ∃ w : List (Move n), w.length ≤ C * es.length ∧
        ∀ s, ((s ∈ P ∧ d.val s = solved n s) ∨ ∃ e ∈ es, s ∈ R e) →
          applyWord w d.val s = solved n s := by
    induction es with
    | nil =>
      intro d
      refine ⟨[], by simp, ?_⟩
      intro s hs
      rcases hs with hs | ⟨e, he, _⟩
      · exact hs.2
      · simp at he
    | cons e es ih =>
      intro d
      obtain ⟨u, hu, hsol⟩ := ih d
      obtain ⟨v, hv, hvR, hvP⟩ := hstep e (advance d u)
      refine ⟨u ++ v, ?_, ?_⟩
      · simp only [List.length_append, List.length_cons]
        calc
          u.length + v.length ≤ C * es.length + C := Nat.add_le_add hu hv
          _ = C * (es.length + 1) := by ring
      · intro s hs
        rw [happ]
        change applyWord v (advance d u).val s = solved n s
        rcases hs with hs | ⟨j, hj, hjs⟩
        · exact hvP s hs.1 (hsol s (Or.inl hs))
        · rcases List.mem_cons.mp hj with he | hj
          · subst j
            exact hvR s hjs
          · exact hvP s (hR j hjs) (hsol s (Or.inr ⟨j, hj, hjs⟩))
  obtain ⟨w, hw, hsol⟩ := sweep (Finset.univ.toList : List E) c
  refine ⟨w, by simpa using hw, ?_⟩
  intro s hs
  apply hsol s
  rcases hs with hs | ⟨e, he⟩
  · exact Or.inl hs
  · exact Or.inr ⟨e, by simp, he⟩
