import RubikSTM.Definitions.OBTM.Global.RectangleCompiler
import RubikSTM.Lemmas.GlobalWords.GenericLocalRecolour
import RubikSTM.Lemmas.GlobalWords.ExceptionalPreprocessing
import RubikSTM.Lemmas.GlobalWords.RegionSame
import RubikSTM.Lemmas.GlobalWords.RegionsDisjoint
import RubikSTM.Lemmas.GlobalWords.GlobalCover
import RubikSTM.Lemmas.GlobalWords.UndoWord
import RubikSTM.Lemmas.Payloads.InverseWordPermutation
import RubikSTM.Lemmas.OBTM.Global.SequentialRecolour
import RubikSTM.Lemmas.OBTM.Global.RecolourFromStm
import RubikSTM.Lemmas.OBTM.Global.ApplyBlockWordAppend
import RubikSTM.Lemmas.OBTM.SliceWordToBlocks
set_option autoImplicit false

theorem proof_RubikOBTM_Global_finite_global_block_word_bound : ∃ C : ℕ, ∀ (n : ℕ), 2 ≤ n →
    ∀ (h : ℕ) (f : RubikGlobal.I n → Fin h)
      (rcost : RubikGlobalWord.GroupPair h → ℕ),
    (∀ (p : RubikGlobalWord.GroupPair h) (c d : Rubik.Position n),
      ∃ w : List (RubikOBTM.BlockMove n), w.length ≤ rcost p ∧
        RubikOBTM.Global.Recolour (RubikGlobalWord.Region f (Sum.inl p)) c.val d.val w) →
    ∀ c d : Rubik.Position n, ∃ w : List (RubikOBTM.BlockMove n),
      w.length ≤ (∑ p, rcost p) +
        C * (RubikGlobalWord.sameCount f + 6 * Fintype.card (RubikGlobal.I n)) +
        4 * RubikCore.cleanupBound ∧
      RubikOBTM.applyBlockWord w c.val = d.val := by
  classical
  obtain ⟨K,hK⟩ := RubikGlobalWord.generic_local_recolour
  obtain ⟨P,hP⟩ := RubikGlobalWord.exceptional_preprocessing
  refine ⟨2*(P+K),?_⟩
  intro n hn h f rcost hrect c d
  obtain ⟨u,hu,hU⟩ := hP n c
  obtain ⟨v,hv,hV⟩ := hP n d
  let c' := RubikGlobalWord.advance c u
  let d' := RubikGlobalWord.advance d v
  let cost : RubikGlobalWord.Task f → ℕ :=
    Sum.elim rcost (fun _ => 2*K)
  let rows := (Finset.univ : Finset (RubikGlobalWord.Task f)).toList
  have sol : ∀ t ∈ rows, ∀ x : Rubik.Position n, ∃ w : List (RubikOBTM.BlockMove n),
      w.length ≤ cost t ∧ RubikOBTM.Global.Recolour (RubikGlobalWord.Region f t) x.val d'.val w := by
    intro t ht x
    rcases t with p | p
    · exact hrect p x d'
    · obtain ⟨u,hu,hm⟩ := hK n p.val x d'
      obtain ⟨w,hw,hW⟩ := RubikOBTM.Global.recolour_from_stm hn
        (RubikGlobal.GenericRange p.val) x.val d'.val u hm
      exact ⟨w,hw.trans (Nat.mul_le_mul_left 2 hu),
        by simpa only [RubikGlobalWord.region_same] using hW⟩
  have dis : ∀ t ∈ rows, ∀ z ∈ rows, t ≠ z →
      Disjoint (RubikGlobalWord.Region f t) (RubikGlobalWord.Region f z) := by
    intro t ht z hz htz
    exact RubikGlobalWord.regions_disjoint f t z htz
  obtain ⟨w,hw,hWunion⟩ := RubikOBTM.Global.sequential_recolour
    (RubikGlobalWord.Region f) cost d' rows (Finset.nodup_toList _) dis sol c'
  have hW : RubikOBTM.Global.Recolour
      {s | ∃ t ∈ rows, s ∈ RubikGlobalWord.Region f t} c'.val d'.val w := by
    simpa only [RubikOBTM.Global.Recolour, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] using hWunion
  have hsum : (rows.map cost).sum =
      (∑ p : RubikGlobalWord.GroupPair h, rcost p) +
        RubikGlobalWord.sameCount f*(2*K) := by
    rw [← List.sum_toFinset cost (Finset.nodup_toList _)]
    simp only [rows,Finset.toList_toFinset,Fintype.sum_sum_type,cost,Sum.elim_inl,Sum.elim_inr,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul,RubikGlobalWord.sameCount]
    simp
  rw [hsum] at hw
  have heq : RubikOBTM.applyBlockWord w c'.val = d'.val := by
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
  obtain ⟨ub,hub,hUb⟩ := RubikOBTM.sliceWord_to_blocks hn u
  obtain ⟨vb,hvb,hVb⟩ := RubikOBTM.sliceWord_to_blocks hn (RubikPayload.inverseWord v)
  have hvb' : vb.length ≤ 2*v.length := by
    simpa only [(RubikPayload.inverseWordPermutation v).2] using hvb
  refine ⟨ub++w++vb,?_,?_⟩
  · simp only [List.length_append]
    nlinarith [Nat.zero_le (P*RubikGlobalWord.sameCount f),
      Nat.zero_le (K*(6*Fintype.card (RubikGlobal.I n)))]
  · rw [RubikOBTM.Global.applyBlockWord_append,RubikOBTM.Global.applyBlockWord_append,hUb]
    change RubikOBTM.applyBlockWord vb (RubikOBTM.applyBlockWord w c'.val) = d.val
    rw [heq,hVb]
    exact RubikGlobalWord.undo_word v d.val
