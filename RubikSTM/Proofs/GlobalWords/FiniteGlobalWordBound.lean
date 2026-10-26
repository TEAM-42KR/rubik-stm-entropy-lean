import Mathlib
import RubikSTM.Definitions.GlobalWords.Region
import RubikSTM.Definitions.Core.CoreAction
import RubikSTM.Lemmas.GlobalWords.RectangleRecolour
import RubikSTM.Lemmas.GlobalWords.GenericLocalRecolour
import RubikSTM.Lemmas.GlobalWords.ExceptionalPreprocessing
import RubikSTM.Lemmas.GlobalWords.GroupsAdmissible
import RubikSTM.Lemmas.GlobalWords.RegionRectangle
import RubikSTM.Lemmas.GlobalWords.RegionSame
import RubikSTM.Lemmas.GlobalWords.RegionsDisjoint
import RubikSTM.Lemmas.GlobalWords.SequentialRecolour
import RubikSTM.Lemmas.GlobalWords.GlobalCover
import RubikSTM.Lemmas.GlobalWords.UndoWord
import RubikSTM.Lemmas.Payloads.InverseWordPermutation
import RubikSTM.Lemmas.Geometry.ApplyWordAppend
set_option autoImplicit false

theorem proof_RubikGlobalWord_finite_global_word_bound : ∃ C R : ℕ, ∀ (n h : ℕ) (f : RubikGlobal.I n → Fin h)
  (k M : RubikGlobalWord.GroupPair h → ℕ) (L : ℕ), 0 < L → 4 ∣ L →
  ∀ B : (p : RubikGlobalWord.GroupPair h) → RubikCodebook.Book RubikChannel.Paired.Letter (k p) L,
    (∀ p, 0 < k p) → (∀ p, RubikCodebook.CoversAll RubikChannel.Paired.act (B p)) →
    (∀ p (i : Fin L), ((B p) i).card ≤ M p) →
  ∀ c d : Rubik.Position n, ∃ w : List (Rubik.Move n),
    w.length ≤ (∑ p : RubikGlobalWord.GroupPair h, RubikGlobalWord.rectangleCost R f k M L p) +
      C*(RubikGlobalWord.sameCount f+6*Fintype.card (RubikGlobal.I n)) + 2*RubikCore.cleanupBound ∧
    Rubik.applyWord w c.val = d.val := by
  classical
  obtain ⟨R,hR⟩ := RubikGlobalWord.rectangle_recolour
  obtain ⟨K,hK⟩ := RubikGlobalWord.generic_local_recolour
  obtain ⟨P,hP⟩ := RubikGlobalWord.exceptional_preprocessing
  refine ⟨P+K,R,?_⟩
  intro n h f k M L hL hL4 B hk hB hM c d
  obtain ⟨u,hu,hU⟩ := hP n c
  obtain ⟨v,hv,hV⟩ := hP n d
  let c' := RubikGlobalWord.advance c u
  let d' := RubikGlobalWord.advance d v
  let cost : RubikGlobalWord.Task f → ℕ :=
    Sum.elim (RubikGlobalWord.rectangleCost R f k M L) (fun _ => K)
  let rows := (Finset.univ : Finset (RubikGlobalWord.Task f)).toList
  have sol : ∀ t ∈ rows, ∀ x : Rubik.Position n, ∃ w : List (Rubik.Move n),
      w.length ≤ cost t ∧ RubikGlobalWord.Recolour (RubikGlobalWord.Region f t) x.val d'.val w := by
    intro t ht x
    rcases t with p | p
    · obtain ⟨w,hw,hm⟩ := hR n (RubikGlobalWord.depthGroup f p.val.1)
        (RubikGlobalWord.depthGroup f p.val.2) (RubikGlobalWord.groups_admissible f p)
        (k p) L (M p) (hk p) hL hL4 (B p) (hB p) (hM p) x d'
      exact ⟨w,hw,by simpa only [RubikGlobalWord.region_rectangle] using hm⟩
    · obtain ⟨w,hw,hm⟩ := hK n p.val x d'
      exact ⟨w,hw,by simpa only [RubikGlobalWord.region_same] using hm⟩
  have dis : ∀ t ∈ rows, ∀ z ∈ rows, t ≠ z →
      Disjoint (RubikGlobalWord.Region f t) (RubikGlobalWord.Region f z) := by
    intro t ht z hz htz
    exact RubikGlobalWord.regions_disjoint f t z htz
  obtain ⟨w,hw,hW⟩ := RubikGlobalWord.sequential_recolour
    (RubikGlobalWord.Region f) cost d' rows (Finset.nodup_toList _) dis sol c'
  have hsum : (rows.map cost).sum =
      (∑ p : RubikGlobalWord.GroupPair h, RubikGlobalWord.rectangleCost R f k M L p) +
        RubikGlobalWord.sameCount f*K := by
    rw [← List.sum_toFinset cost (Finset.nodup_toList _)]
    simp only [rows,Finset.toList_toFinset,Fintype.sum_sum_type,cost,Sum.elim_inl,Sum.elim_inr,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul,RubikGlobalWord.sameCount]
    simp
  rw [hsum] at hw
  have heq : Rubik.applyWord w c'.val = d'.val := by
    funext s
    by_cases hs : ∃ t : RubikGlobalWord.Task f, s ∈ RubikGlobalWord.Region f t
    · obtain ⟨t,ht⟩ := hs
      exact hW.1 s ⟨t,by simp [rows],ht⟩
    · have hn : RubikGlobalWord.Nongeneric s := by
        rcases RubikGlobalWord.global_cover f s with hn | ht
        · exact hn
        · exact (hs ht).elim
      have hout : ¬ ∃ t ∈ rows, s ∈ RubikGlobalWord.Region f t := by
        rintro ⟨t,ht,hs'⟩
        exact hs ⟨t,hs'⟩
      exact (hW.2 s hout).trans ((hU s hn).trans (hV s hn).symm)
  refine ⟨u++w++RubikPayload.inverseWord v,?_,?_⟩
  · simp only [List.length_append,(RubikPayload.inverseWordPermutation v).2]
    nlinarith [Nat.zero_le (P*RubikGlobalWord.sameCount f),
      Nat.zero_le (K*(6*Fintype.card (RubikGlobal.I n)))]
  · rw [Rubik.applyWord_append,Rubik.applyWord_append]
    change Rubik.applyWord (RubikPayload.inverseWord v) (Rubik.applyWord w c'.val) = d.val
    rw [heq]
    exact RubikGlobalWord.undo_word v d.val

#print axioms proof_RubikGlobalWord_finite_global_word_bound
