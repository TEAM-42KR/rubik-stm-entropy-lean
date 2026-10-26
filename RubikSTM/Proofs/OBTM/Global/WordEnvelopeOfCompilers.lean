import RubikSTM.Definitions.OBTM.Global.RectangleCompiler
import RubikSTM.Definitions.OBTM.Grouping.GroupOf
import RubikSTM.Lemmas.OBTM.Global.FiniteGlobalBlockWordBound
import RubikSTM.Lemmas.OBTM.Global.DependentSumGroupPairs
import RubikSTM.Lemmas.OBTM.Global.CleanupScalarBound
import RubikSTM.Lemmas.OBTM.Grouping.ActualScalarFacts
import RubikSTM.Lemmas.OBTM.Grouping.DepthGroupLink
import RubikSTM.Lemmas.OBTM.Grouping.DepthGroupInterval
import RubikSTM.Lemmas.GlobalWords.GroupsAdmissible
import RubikSTM.Lemmas.GlobalWords.RegionRectangle
import RubikSTM.Lemmas.OBTM.WordBounds.EventuallyBlockLarge
import RubikSTM.Lemmas.OBTM.WordBounds.RowCeilEqNatCeil
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
open Filter Topology RubikCostBridge

theorem proof_RubikOBTM_Global_wordEnvelope_of_compilers (hrect : RubikOBTM.Global.RectangleCompiler)
    (hbooks : RubikOBTM.Global.BookSupply) : RubikOBTM.Global.WordCostEnvelope := by
  classical
  obtain ⟨R,hR⟩ := hrect
  obtain ⟨C,hglobal⟩ := RubikOBTM.Global.finite_global_block_word_bound
  have hT : 0 < RubikOBTM.Finite.period := Fintype.card_pos
  intro η hη
  obtain ⟨L,ρ,K,hL,hL4,hρ,hLρ,hBook⟩ := hbooks η hη
  have hCexc : 0 ≤ 6*(C:ℝ)+4*(RubikCore.cleanupBound:ℝ) :=
    add_nonneg
      (mul_nonneg (show (0:ℝ) ≤ 6 by norm_num) (Nat.cast_nonneg C))
      (mul_nonneg (show (0:ℝ) ≤ 4 by norm_num) (Nat.cast_nonneg RubikCore.cleanupBound))
  refine ⟨L,ρ,R,C,6*(C:ℝ)+4*(RubikCore.cleanupBound:ℝ),Nat.cast_nonneg L,hρ,
    Nat.cast_nonneg R,Nat.cast_nonneg C,hCexc,hLρ,?_⟩
  filter_upwards [RubikCostBridge.eventually_block_large ρ hρ K,eventually_ge_atTop 2]
    with n hn hn2
  obtain ⟨hh,hscale⟩ := hn
  let H := hNat n
  let f := RubikOBTM.Grouping.groupOf (mNat n) H hh
  let r : Fin H → ℕ := fun i => (RubikGlobalWord.depthGroup f i).card
  obtain ⟨hbal,hpairs,hcnt⟩ := RubikOBTM.Grouping.actual_scalar_facts n H hh
  change (∀ i, mNat n / H ≤ r i ∧ r i ≤ mNat n / H + 1) at hbal
  let k (p : RubikGlobalWord.GroupPair H) := block ρ (r p.val.2)
  have hk (p : RubikGlobalWord.GroupPair H) : K ≤ k p ∧ 0 < k p := by
    have ht := hscale (r p.val.2) (hbal p.val.2).1
    exact ⟨(le_max_left K 1).trans ht, (le_max_right K 1).trans ht⟩
  have hb (p : RubikGlobalWord.GroupPair H) := hBook hT (k p) (hk p).1
  choose B hcover hB using hb
  let Mnat (p : RubikGlobalWord.GroupPair H) := ⌊Real.exp ((k p : ℝ)*ρ)⌋₊
  have hM (p : RubikGlobalWord.GroupPair H) (i : Fin L) : ((B p) i).card ≤ Mnat p := by
    apply (Nat.le_floor_iff (Real.exp_nonneg _)).mpr
    exact hB p i
  let M (i j : Fin H) : ℝ := if hp : i < j then Mnat ⟨(i,j),hp⟩ else 0
  have hY (t : Fin H) : Set.OrdConnected (RubikGlobalWord.depthGroup f t : Set (Fin n)) := by
    dsimp only [f,mNat]
    rw [← (RubikOBTM.Grouping.depthGroup_link n H hh t).1]
    by_cases hg : (RubikOBTM.Grouping.group ((n-2)/2) H hh t).Nonempty
    · obtain ⟨hI,hlo,hlu,hhi⟩ := RubikOBTM.Grouping.depthGroup_interval n H hh t hg
      rw [hI]
      constructor
      intro x hx y hy z hz
      have hx' : RubikOBTM.Grouping.lower ((n-2)/2) H hh t hg ≤ x.val ∧
          x.val ≤ RubikOBTM.Grouping.upper ((n-2)/2) H hh t hg := by simpa using hx
      have hy' : RubikOBTM.Grouping.lower ((n-2)/2) H hh t hg ≤ y.val ∧
          y.val ≤ RubikOBTM.Grouping.upper ((n-2)/2) H hh t hg := by simpa using hy
      have hz' : x.val ≤ z.val ∧ z.val ≤ y.val := hz
      simpa using And.intro (hx'.1.trans hz'.1) (hz'.2.trans hy'.2)
    · have he : RubikOBTM.Grouping.group ((n-2)/2) H hh t = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hg
      simp only [RubikOBTM.Grouping.depthGroup,he,Finset.image_empty,Finset.coe_empty]
      exact ⟨by intro x hx; exact hx.elim⟩
  let rcost (p : RubikGlobalWord.GroupPair H) :=
    RubikGlobalWord.rectangleCost R f k Mnat L p
  have hrectangles (p : RubikGlobalWord.GroupPair H) (c d : Rubik.Position n) :
      ∃ w : List (RubikOBTM.BlockMove n), w.length ≤ rcost p ∧
        RubikOBTM.Global.Recolour (RubikGlobalWord.Region f (Sum.inl p)) c.val d.val w := by
    obtain ⟨w,hw,hm⟩ := hR n (RubikGlobalWord.depthGroup f p.val.1)
      (RubikGlobalWord.depthGroup f p.val.2) (RubikGlobalWord.groups_admissible f p)
      (hY p.val.2) (k p) L (Mnat p) (hk p).2 hL hL4 hT (B p) (hcover p) (hM p) c d
    exact ⟨w,hw,by rw [RubikGlobalWord.region_rectangle f p]; exact hm⟩
  refine ⟨H,r,M,(RubikGlobalWord.sameCount f : ℝ),?_,hpairs,hcnt,?_,?_⟩
  · simpa only [m,h,Nat.floor_div_eq_div] using hbal
  · intro i j
    dsimp [M]
    split_ifs with hp
    · simpa only [Mnat,k,mul_comm] using Nat.floor_le (Real.exp_nonneg ((k ⟨(i,j),hp⟩ : ℝ)*ρ))
    · exact (Real.exp_pos _).le
  · intro c d
    obtain ⟨w,hw,he⟩ := hglobal n hn2 H f rcost hrectangles c d
    refine ⟨w,?_,he⟩
    have hsum : (((∑ p : RubikGlobalWord.GroupPair H,
          RubikGlobalWord.rectangleCost R f k Mnat L p) : ℕ) : ℝ) =
        ∑ i : Fin H, ∑ j : Fin H, if i < j then
          (L : ℝ) * ((⌈(r i : ℝ) / (block ρ (r j) : ℝ)⌉₊ : ℝ) + 3) *
            ((r j : ℝ) + (R : ℝ) * ((block ρ (r j) : ℝ) + 1) * M i j)
          else 0 := by
      rw [Nat.cast_sum,RubikOBTM.Global.dependent_sum_group_pairs]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i < j
      · simp only [hij,if_pos,dite_true]
        simp only [RubikGlobalWord.rectangleCost,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,
          RubikCostBridge.rowCeil_eq_natCeil _ _ (hk ⟨(i,j),hij⟩).2]
        dsimp only [k]
        simp only [M,dif_pos hij]
        rfl
      · simp [hij]
    have hcleanup := RubikOBTM.Global.cleanup_scalar_bound C RubikCore.cleanupBound
      (mNat n) (RubikGlobalWord.sameCount f) n
      (by dsimp [mNat]; omega) (by omega)
    have hd : (w.length : ℝ) ≤
        (((∑ p : RubikGlobalWord.GroupPair H,
          RubikGlobalWord.rectangleCost R f k Mnat L p) : ℕ) : ℝ) +
        ((C*(RubikGlobalWord.sameCount f+6*Fintype.card (RubikGlobal.I n)) +
          4*RubikCore.cleanupBound : ℕ) : ℝ) := by
      have hdCast : (w.length : ℝ) ≤
          (((∑ p, rcost p) + C*(RubikGlobalWord.sameCount f+
            6*Fintype.card (RubikGlobal.I n)) + 4*RubikCore.cleanupBound : ℕ) : ℝ) :=
        Nat.cast_le.mpr hw
      simpa only [rcost,Nat.cast_add,add_assoc] using hdCast
    have hcleanup_actual :
        ((C*(RubikGlobalWord.sameCount f+6*Fintype.card (RubikGlobal.I n)) +
          4*RubikCore.cleanupBound : ℕ) : ℝ) ≤
        (C:ℝ)*(RubikGlobalWord.sameCount f:ℝ) +
          (6*(C:ℝ)+4*(RubikCore.cleanupBound:ℝ))*(n:ℝ) := by
      simpa only [Fintype.card_fin,mNat] using hcleanup
    have ht := hd.trans (add_le_add (le_refl _) hcleanup_actual)
    rw [hsum] at ht
    simpa only [add_assoc] using ht
