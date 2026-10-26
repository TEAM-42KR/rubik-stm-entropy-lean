import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
import RubikSTM.Definitions.Core.CoreAction
import RubikSTM.Lemmas.Geometry.ApplyWordAppend
set_option autoImplicit false

theorem proof_RubikGlobalWord_sequential_recolour {n : ℕ} {J : Type*} (S : J → Set (Rubik.Sticker n))
  (cost : J → ℕ) (d : Rubik.Position n) (rows : List J) (hnd : rows.Nodup)
  (hdis : ∀ i ∈ rows, ∀ j ∈ rows, i ≠ j → Disjoint (S i) (S j))
  (hsolve : ∀ i ∈ rows, ∀ c : Rubik.Position n, ∃ w : List (Rubik.Move n),
    w.length ≤ cost i ∧ RubikGlobalWord.Recolour (S i) c.val d.val w) :
  ∀ c : Rubik.Position n, ∃ w : List (Rubik.Move n),
    w.length ≤ (rows.map cost).sum ∧
      RubikGlobalWord.Recolour {s | ∃ i ∈ rows, s ∈ S i} c.val d.val w := by
  classical
  revert hnd hdis hsolve
  induction rows with
  | nil =>
    intro hnd hdis hsolve c
    refine ⟨[],by simp,?_,?_⟩
    · rintro s ⟨i,hi,hs⟩; simp at hi
    · intro s hs; rfl
  | cons i rows ih =>
    intro hnd hdis hsolve c
    obtain ⟨u,hu,hU⟩ := hsolve i (by simp) c
    have hds : ∀ a ∈ rows, ∀ b ∈ rows, a ≠ b → Disjoint (S a) (S b) := by
      intro a ha b hb hab
      exact hdis a (by simp [ha]) b (by simp [hb]) hab
    have hsols : ∀ a ∈ rows, ∀ c : Rubik.Position n, ∃ w : List (Rubik.Move n),
        w.length ≤ cost a ∧ RubikGlobalWord.Recolour (S a) c.val d.val w := by
      intro a ha c
      exact hsolve a (by simp [ha]) c
    obtain ⟨v,hv,hV⟩ := ih (List.nodup_cons.mp hnd).2 hds hsols (RubikGlobalWord.advance c u)
    refine ⟨u++v,?_,?_,?_⟩
    · simp only [List.length_append,List.map_cons,List.sum_cons]
      exact Nat.add_le_add hu hv
    · rintro s ⟨j,hj,hs⟩
      rw [Rubik.applyWord_append]
      rcases List.mem_cons.mp hj with he | ht
      · subst j
        have hn : ¬ ∃ j ∈ rows, s ∈ S j := by
          rintro ⟨j,hj,hsj⟩
          have hne : i≠j := by intro he; subst j; exact (List.nodup_cons.mp hnd).1 hj
          exact Set.disjoint_left.mp (hdis i (by simp) j (by simp [hj]) hne) hs hsj
        exact (hV.2 s hn).trans (hU.1 s hs)
      · exact hV.1 s ⟨j,ht,hs⟩
    · intro s hs
      rw [Rubik.applyWord_append]
      have hni : s ∉ S i := by intro hi; exact hs ⟨i,by simp,hi⟩
      have hnr : ¬ ∃ j ∈ rows, s ∈ S j := by
        rintro ⟨j,hj,hss⟩; exact hs ⟨j,by simp [hj],hss⟩
      exact (hV.2 s hnr).trans (hU.2 s hni)

#print axioms proof_RubikGlobalWord_sequential_recolour
