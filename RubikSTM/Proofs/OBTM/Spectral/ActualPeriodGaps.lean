import RubikSTM.Definitions.OBTM.Finite.DoubledSubgroup
import RubikSTM.Definitions.OBTM.Spectral.ActualPeriodPositive
import RubikSTM.Definitions.OBTM.Spectral.PhaseKernel
set_option autoImplicit false

open RubikOBTM.Finite Equiv Equiv.Perm
open scoped Classical
private theorem RubikChannel.Colour.AlternatingTransitive {V Colour : Type*} [Fintype V] [DecidableEq V] (κ : V → Colour)
    (ρ : Equiv.Perm V) (hρ : sign ρ = -1) (hκ : κ ∘ ρ = κ)
    (x y : RubikChannel.Colour.Orbit κ) :
    ∃ σ ∈ alternatingGroup V, RubikChannel.Colour.orbitAction κ σ x = y := by
  have evenRep (f : RubikChannel.Colour.Orbit κ) :
      ∃ σ ∈ alternatingGroup V, f.val = κ ∘ σ := by
    obtain ⟨σ, hσ⟩ := f.property
    rcases Int.units_eq_one_or (sign σ) with hs | hs
    · exact ⟨σ, mem_alternatingGroup.mpr hs, hσ⟩
    · refine ⟨ρ * σ, mem_alternatingGroup.mpr (by simp [hρ, hs]), ?_⟩
      rw [hσ]
      funext i
      exact (congrFun hκ (σ i)).symm
  obtain ⟨σ, hσ, hx⟩ := evenRep x
  obtain ⟨τ, hτ, hy⟩ := evenRep y
  refine ⟨τ⁻¹ * σ, (alternatingGroup V).mul_mem ((alternatingGroup V).inv_mem hτ) hσ, ?_⟩
  apply Subtype.ext
  funext i
  change x.val ((τ⁻¹ * σ)⁻¹ i) = y.val i
  rw [hx, hy]
  simp [Function.comp_def]

open RubikOBTM.Finite Equiv Equiv.Perm

private theorem RubikOBTM.Finite.transitive (x y : Z) : ∃ g : G, act g x = y := by
  have hsign : sign (swap (0 : Fin 24) 1) = -1 := by simp
  have hseed : RubikChannel.Paired.Seed ∘ swap (0 : Fin 24) 1 = RubikChannel.Paired.Seed := by decide
  obtain ⟨σ,hσ,hx⟩ := RubikChannel.Colour.AlternatingTransitive
    RubikChannel.Paired.Seed (swap 0 1) hsign hseed x.1 y.1
  obtain ⟨τ,hτ,hy⟩ := RubikChannel.Colour.AlternatingTransitive
    RubikChannel.Paired.Seed (swap 0 1) hsign hseed x.2 y.2
  exact ⟨(⟨σ,hσ⟩,⟨τ,hτ⟩),Prod.ext hx hy⟩

open RubikOBTM.Finite

private theorem RubikOBTM.Finite.base_injective : Function.Injective base := by
  have h : ∀ u v : Toggle, togglePerm u = togglePerm v → u = v := by decide
  intro u v huv
  exact h u v (congrArg Subtype.val huv)

open RubikOBTM.Finite

private theorem RubikOBTM.Finite.native_basic : Fintype.card Toggle = 4 ∧ Fintype.card Native = 9 ∧
    (∀ v : Toggle, v * v = 1) ∧ ∀ u v : Toggle, u * v = v * u := by
  exact ⟨by decide,by decide,by decide,by decide⟩

open RubikOBTM.Finite

private theorem RubikOBTM.Finite.relative_surjective (i : Phase) (g : G) (hg : g ∈ K i) :
    ∃ c d : Native, letter i c * (letter i d)⁻¹ = g := by
  have hsmall : ∀ v : Toggle, ∃ c d : Nonzero, c.val * d.val⁻¹ = v := by decide
  obtain ⟨u,hu⟩ := hg.1
  obtain ⟨v,hv⟩ := hg.2
  obtain ⟨a,b,hab⟩ := hsmall u
  obtain ⟨c,d,hcd⟩ := hsmall v
  refine ⟨(a,c),(b,d),Prod.ext ?_ ?_⟩
  · change embed i a.val * (embed i b.val)⁻¹ = g.1
    rw [← map_inv, ← map_mul, hab, hu]
  · change embed i c.val * (embed i d.val)⁻¹ = g.2
    rw [← map_inv, ← map_mul, hcd, hv]

open RubikOBTM.Finite

private theorem RubikOBTM.Finite.phase_abelian (i : Phase) (g h : G) (hg : g ∈ K i) (hh : h ∈ K i) : g * h = h * g := by
  obtain ⟨u,hu⟩ := hg.1
  obtain ⟨v,hv⟩ := hg.2
  obtain ⟨a,ha⟩ := hh.1
  obtain ⟨b,hb⟩ := hh.2
  apply Prod.ext
  · change g.1 * h.1 = h.1 * g.1
    rw [← hu,← ha,← map_mul,← map_mul,mul_comm u a]
  · change g.2 * h.2 = h.2 * g.2
    rw [← hv,← hb,← map_mul,← map_mul,mul_comm v b]

open RubikOBTM.Finite

private theorem RubikOBTM.Finite.normal_E (i : Phase) : Subgroup.normalClosure (E i : Set A) = ⊤ := by
  letI : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by simp [Nat.card_eq_fintype_card])
  let u : Toggle := Multiplicative.ofAdd (1,0)
  have hu : u ≠ 1 := by decide
  have hbase : base u ≠ 1 := by
    intro hh
    apply hu
    exact RubikOBTM.Finite.base_injective (hh.trans base.map_one.symm)
  have hnon : embed i u ≠ 1 := by
    intro hh
    apply hbase
    have hi := congrArg (fun z => (MulAut.conj i).symm z) hh
    simpa [embed, mul_assoc] using hi
  have hmem : embed i u ∈ Subgroup.normalClosure (E i : Set A) :=
    Subgroup.subset_normalClosure ⟨u,rfl⟩
  rcases (Subgroup.normalClosure_normal (s := (E i : Set A))).eq_bot_or_eq_top with h | h
  · rw [h,Subgroup.mem_bot] at hmem
    exact (hnon hmem).elim
  · exact h

open RubikOBTM.Finite

private theorem RubikOBTM.Finite.normal_K (i : Phase) : Subgroup.normalClosure (K i : Set G) = ⊤ := by
  let H := Subgroup.normalClosure (K i : Set G)
  let f : A →* G := (MonoidHom.id A).prod (1 : A →* A)
  let g : A →* G := (1 : A →* A).prod (MonoidHom.id A)
  have hf : Subgroup.normalClosure (E i : Set A) ≤ H.comap f := by
    apply Subgroup.normalClosure_le_normal
    intro x hx
    exact Subgroup.subset_normalClosure (show f x ∈ K i from ⟨hx,(E i).one_mem⟩)
  have hg : Subgroup.normalClosure (E i : Set A) ≤ H.comap g := by
    apply Subgroup.normalClosure_le_normal
    intro x hx
    exact Subgroup.subset_normalClosure (show g x ∈ K i from ⟨(E i).one_mem,hx⟩)
  rw [RubikOBTM.Finite.normal_E] at hf hg
  apply top_unique
  intro x hx
  have h1 : f x.1 ∈ H := hf (Subgroup.mem_top _)
  have h2 : g x.2 ∈ H := hg (Subgroup.mem_top _)
  simpa [f,g] using H.mul_mem h1 h2

open RubikOBTM.Finite

private theorem RubikOBTM.Finite.union_generation : Subgroup.closure (⋃ i : Phase, (K i : Set G)) = ⊤ := by
  let H := Subgroup.closure (⋃ i : Phase, (K i : Set G))
  let f : A →* G := (MonoidHom.id A).prod (1 : A →* A)
  let g : A →* G := (1 : A →* A).prod (MonoidHom.id A)
  have hleft : Subgroup.normalClosure (E 1 : Set A) ≤ H.comap f := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    obtain ⟨y,hy,hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c,hc⟩ := isConj_iff.mp hconj
    obtain ⟨v,hv⟩ := hy
    have hex : x ∈ E c := by
      refine ⟨v,?_⟩
      change c * base v * c⁻¹ = x
      have hb : base v = y := by simpa [embed] using hv
      simpa only [hb] using hc
    exact Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨c,show f x ∈ K c from ⟨hex,(E c).one_mem⟩⟩)
  have hright : Subgroup.normalClosure (E 1 : Set A) ≤ H.comap g := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    obtain ⟨y,hy,hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c,hc⟩ := isConj_iff.mp hconj
    obtain ⟨v,hv⟩ := hy
    have hex : x ∈ E c := by
      refine ⟨v,?_⟩
      change c * base v * c⁻¹ = x
      have hb : base v = y := by simpa [embed] using hv
      simpa only [hb] using hc
    exact Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨c,show g x ∈ K c from ⟨(E c).one_mem,hex⟩⟩)
  rw [RubikOBTM.Finite.normal_E] at hleft hright
  apply top_unique
  intro x hx
  have h1 : f x.1 ∈ H := hleft (Subgroup.mem_top _)
  have h2 : g x.2 ∈ H := hright (Subgroup.mem_top _)
  simpa [f,g] using H.mul_mem h1 h2

open RubikOBTM.Finite

open scoped BigOperators Matrix.Norms.L2Operator

private theorem average_norm_equality {C X : Type*} [Fintype C] [Fintype X] [DecidableEq X]
    (μ : RubikJanson.FiniteLaw C) (hμ : ∀ c, 0 < μ.weight c)
    (σ : C → Equiv.Perm X) (v : EuclideanSpace ℝ X)
    (hv : ‖Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=X) (RubikChannel.transition μ σ) v‖ = ‖v‖) :
    ∀ a b x, v.ofLp (σ a x) = v.ofLp (σ b x) := by
  classical
  let a : X → ℝ := fun x => ∑ c, μ.weight c * v.ofLp (σ c x)
  have ha : (Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=X)
      (RubikChannel.transition μ σ) v).ofLp = a := by
    ext x
    simp only [Matrix.ofLp_toEuclideanCLM,Matrix.mulVec, dotProduct,
      RubikChannel.transition,Finset.sum_mul]
    rw [Finset.sum_comm]
    simp [RubikChannel.rowPermutation,a,ite_mul,mul_assoc]
  have hsq : ∑ x, (a x)^2 = ∑ x, (v.ofLp x)^2 := by
    have ht := congrArg (fun t : ℝ => t^2) hv
    simpa only [EuclideanSpace.norm_sq_eq,ha,Real.norm_eq_abs,sq_abs] using ht
  have hstrict := (show Even (2 : ℕ) by decide).strictConvexOn_pow (by decide : (2:ℕ) ≠ 0)
  have hj (x : X) : (a x)^2 ≤ ∑ c, μ.weight c * (v.ofLp (σ c x))^2 := by
    simpa only [smul_eq_mul] using hstrict.convexOn.map_sum_le
      (fun c _ => (hμ c).le) μ.total (fun _ _ => Set.mem_univ _)
  have he : ∑ x, (∑ c, μ.weight c * (v.ofLp (σ c x))^2 - (a x)^2) = 0 := by
    rw [Finset.sum_sub_distrib, hsq, Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (Equiv.sum_comp (σ _) (fun x => (v.ofLp x)^2))]
    rw [← Finset.sum_mul, μ.total, one_mul, sub_self]
  have hz (x : X) : ∑ c, μ.weight c * (v.ofLp (σ c x))^2 = (a x)^2 := by
    exact sub_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun x _ => sub_nonneg.mpr (hj x))).mp he x (Finset.mem_univ x))
  intro c d x
  exact (hstrict.map_sum_eq_iff_of_pos (fun c _ => hμ c) μ.total
    (fun _ _ => Set.mem_univ _)).mp (by simpa only [smul_eq_mul] using (hz x).symm)
      (Finset.mem_univ c) (Finset.mem_univ d)

private theorem transition_stochastic {C X : Type*} [Fintype C] [Fintype X] [DecidableEq X]
    (μ : RubikJanson.FiniteLaw C) (act : C → Equiv.Perm X) :
    RubikChannel.transition μ act ∈ doublyStochastic ℝ X := by
  classical
  apply mem_doublyStochastic_iff_sum.mpr
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    apply Finset.sum_nonneg
    intro c _
    apply mul_nonneg (μ.nonneg c)
    simp only [RubikChannel.rowPermutation]
    split <;> norm_num
  · intro x
    change (∑ y, ∑ c, μ.weight c * RubikChannel.rowPermutation (act c) x y) = 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simpa [RubikChannel.rowPermutation, eq_comm] using μ.total
  · intro y
    change (∑ x, ∑ c, μ.weight c * RubikChannel.rowPermutation (act c) x y) = 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simpa [RubikChannel.rowPermutation, Equiv.apply_eq_iff_eq_symm_apply] using μ.total

open scoped Matrix.Norms.L2Operator BigOperators
open RubikOBTM.Spectral

private theorem RubikOBTM.Spectral.phase_norm_rigidity {G C X : Type*} [Group G] [Fintype C] [Fintype X] [DecidableEq X]
    (act : G →* Equiv.Perm X) (K : Subgroup G) (μ : RubikJanson.FiniteLaw C)
    (hμ : ∀ c, 0 < μ.weight c) (letter : C → G) (hmem : ∀ c, letter c ∈ K)
    (hrel : RelativeSurjective K letter) (n : K) :
    phaseKernel act μ letter n ∈ doublyStochastic ℝ X ∧
    ∀ v : EuclideanSpace ℝ X,
      (‖Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=X) (phaseKernel act μ letter n) v‖ = ‖v‖ ↔
        Fixed act K v.ofLp) ∧
      (Fixed act K v.ofLp → Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=X) (phaseKernel act μ letter n) v = v) := by
  classical
  refine ⟨transition_stochastic μ (fun c => act (n.val*letter c)),?_⟩
  intro v
  have hfixed (hf : Fixed act K v.ofLp) :
      Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=X) (phaseKernel act μ letter n) v = v := by
    apply (WithLp.equiv 2 (X → ℝ)).injective
    ext x
    change (Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=X) (phaseKernel act μ letter n) v).ofLp x = v.ofLp x
    simp only [Matrix.ofLp_toEuclideanCLM,Matrix.mulVec,dotProduct,phaseKernel,
      RubikChannel.transition,Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [RubikChannel.rowPermutation,mul_ite,ite_mul,mul_one,mul_zero,zero_mul]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,if_true]
    simp_rw [hf _ (K.mul_mem n.property (hmem _))]
    rw [← Finset.sum_mul,μ.total,one_mul]
  refine ⟨⟨?_,fun hf => by rw [hfixed hf]⟩,hfixed⟩
  intro hv g hg x
  obtain ⟨c,d,hcd⟩ := hrel (n.val⁻¹ * g * n.val)
    (K.mul_mem (K.mul_mem (K.inv_mem n.property) hg) n.property)
  have he := average_norm_equality μ hμ (fun c => act (n.val*letter c)) v hv c d
    (act ((n.val*letter d)⁻¹) x)
  have hid : n.val * letter c * (n.val*letter d)⁻¹ = g := by
    rw [mul_inv_rev,← mul_assoc,show n.val * letter c * (letter d)⁻¹ =
      n.val*(letter c*(letter d)⁻¹) by group, hcd]
    group
  have he' : v.ofLp (act (n.val*letter c*(n.val*letter d)⁻¹) x) = v.ofLp x := by
    simpa [map_mul,map_inv,Equiv.Perm.mul_apply] using he
  rwa [hid] at he'

private theorem compact_strict_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] (A : E →L[ℝ] E)
    (hA : ∀ v, v ≠ 0 → ‖A v‖ < ‖v‖) : ‖A‖ < 1 := by
  have hs : (Metric.sphere (0 : E) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨u,hu,hmax⟩ := (isCompact_sphere (0 : E) 1).exists_isMaxOn hs A.continuous.norm.continuousOn
  have hun : ‖u‖ = 1 := by simpa using hu
  have hlt : ‖A u‖ < 1 := by
    rw [← hun]
    apply hA
    intro hz
    simpa [hz] using hun
  have hbound : ‖A‖ ≤ ‖A u‖ :=
    ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _) (fun v hv =>
      hmax (by simpa using hv))
  exact hbound.trans_lt hlt
open scoped Matrix.Norms.L2Operator BigOperators
open RubikOBTM.Spectral

private theorem RubikOBTM.Spectral.stochastic_strict_from_constants {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (P : Matrix X X ℝ) (hP : P ∈ doublyStochastic ℝ X)
    (heq : ∀ v : EuclideanSpace ℝ X,
      ‖Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=X) P v‖ = ‖v‖ → ∀ x y, v.ofLp x = v.ofLp y) :
    ‖P - averaging‖ < 1 := by
  classical
  let J : Matrix X X ℝ := averaging
  let B : Matrix X X ℝ := 1-J
  let R := Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=X) (P-J)
  have hc : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hJP : J*P=J := by
    ext x y
    change (∑ z, (Fintype.card X : ℝ)⁻¹ * P z y) = _
    rw [← Finset.mul_sum,sum_col_of_mem_doublyStochastic hP y,mul_one]
    rfl
  have hJJ : J*J=J := by ext x y; simp [J,averaging,Matrix.mul_apply,hc]
  have hstar : star J=J := by ext x y; simp [J,averaging,Matrix.star_apply]
  have hB : ‖B‖ ≤ 1 := IsStarProjection.norm_le _ (IsStarProjection.one_sub ⟨hJJ,hstar⟩)
  have hR : P-J=B*P := by dsimp [B]; rw [sub_mul,one_mul,hJP]
  have hp (v : EuclideanSpace ℝ X) :
      ‖Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=X) P v‖ ≤ ‖v‖ := by
    exact (Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=X) P).le_opNorm v |>.trans
      (by rw [Matrix.l2_opNorm_toEuclideanCLM]; nlinarith [Matrix.l2_opNorm_le_one_of_mem_doublyStochastic hP,norm_nonneg v])
  have hr (v : EuclideanSpace ℝ X) : ‖R v‖ ≤ ‖Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=X) P v‖ := by
    dsimp [R]
    rw [hR,map_mul]
    exact (Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=X) B).le_opNorm _ |>.trans
      (by rw [Matrix.l2_opNorm_toEuclideanCLM]; exact mul_le_of_le_one_left (norm_nonneg _) hB)
  have hs (v : EuclideanSpace ℝ X) (hv : v ≠ 0) : ‖R v‖ < ‖v‖ := by
    by_contra hn
    have he : ‖Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=X) P v‖ = ‖v‖ :=
      le_antisymm (hp v) ((not_lt.mp hn).trans (hr v))
    have hconst := heq v he
    let x0 : X := Classical.choice inferInstance
    have hvconst : ∀ x, v.ofLp x = v.ofLp x0 := fun x => hconst x x0
    have hz : R v=0 := by
      apply (WithLp.equiv 2 (X → ℝ)).injective
      ext x
      change Matrix.mulVec (P-J) v.ofLp x=0
      simp only [Matrix.mulVec,dotProduct,hvconst,Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib,
        ← Finset.sum_mul,sum_row_of_mem_doublyStochastic hP x,one_mul]
      simp [J,averaging,hc]
    have hnz := norm_pos_iff.mpr hv
    rw [hz,norm_zero] at hn
    exact hn hnz
  have ht := compact_strict_norm R hs
  simpa only [R,Matrix.l2_opNorm_toEuclideanCLM] using ht

open RubikOBTM.Spectral
open scoped Matrix.Norms.L2Operator BigOperators
open RubikOBTM.Spectral

private theorem RubikOBTM.Spectral.period_gap_from_rigidity {G X : Type*} [Group G] [Fintype X] [DecidableEq X] [Nonempty X] {T : ℕ}
    (act : G →* Equiv.Perm X) (K : Fin T → Subgroup G)
    (hgen : Subgroup.closure (⋃ i, (K i : Set G)) = ⊤)
    (htrans : ∀ x y, ∃ g, act g x=y)
    (A : Fin T → Matrix X X ℝ) (hA : ∀ i, A i ∈ doublyStochastic ℝ X)
    (hrigid : ∀ i (v : EuclideanSpace ℝ X),
      ‖Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=X) (A i) v‖ = ‖v‖ →
        Fixed act (K i) v.ofLp ∧ Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=X) (A i) v=v) :
    ‖period A - averaging‖ < 1 := by
  classical
  have ds_contract
    (P : Matrix X X ℝ) (hP : P ∈ doublyStochastic ℝ X) (v : EuclideanSpace ℝ X) :
    ‖Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=X) P v‖ ≤ ‖v‖ := by
    have hb := (Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=X) P).le_opNorm v
    rw [Matrix.l2_opNorm_toEuclideanCLM] at hb
    nlinarith [Matrix.l2_opNorm_le_one_of_mem_doublyStochastic hP,norm_nonneg v]

  have hlist (l : List (Fin T)) : (l.map A).prod ∈ doublyStochastic ℝ X ∧
      ∀ v : EuclideanSpace ℝ X,
        ‖Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=X) (l.map A).prod v‖ = ‖v‖ →
        (∀ i ∈ l, Fixed act (K i) v.ofLp) ∧
        Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=X) (l.map A).prod v=v := by
    induction l with
    | nil => exact ⟨(doublyStochastic ℝ X).one_mem,fun v _ => ⟨by simp,by simp⟩⟩
    | cons i l ih =>
      refine ⟨by simpa using (doublyStochastic ℝ X).mul_mem (hA i) ih.1,?_⟩
      intro v hv
      have hrest : ‖Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=X) (l.map A).prod v‖ = ‖v‖ := by
        have hfirst := ds_contract (A i) (hA i)
          (Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=X) (l.map A).prod v)
        have hr := ds_contract _ ih.1 v
        simp only [List.map_cons,List.prod_cons,map_mul] at hv
        exact le_antisymm hr (hv ▸ hfirst)
      obtain ⟨hfix,hid⟩ := ih.2 v hrest
      have he : ‖Matrix.toEuclideanCLM (𝕜:=ℝ) (n:=X) (A i) v‖ = ‖v‖ := by
        simpa only [List.map_cons,List.prod_cons,map_mul,ContinuousLinearMap.mul_apply,hid] using hv
      obtain ⟨hfi,hidi⟩ := hrigid i v he
      refine ⟨?_,?_⟩
      · intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hfi
        · exact hfix j hj
      · simpa only [List.map_cons,List.prod_cons,map_mul,ContinuousLinearMap.mul_apply,hid] using hidi
  let l := List.ofFn (fun i : Fin T => i)
  have hl : (l.map A).prod=period A := by simp [l,period,List.map_ofFn,Function.comp_def]
  have hds : period A ∈ doublyStochastic ℝ X := hl ▸ (hlist l).1
  apply stochastic_strict_from_constants (period A) hds
  intro v hv x y
  have hfix (i : Fin T) : Fixed act (K i) v.ofLp :=
    (hlist l).2 v (hl.symm ▸ hv) |>.1 i (by simp [l])
  let S : Subgroup G :=
    { carrier := {g | ∀ x, v.ofLp (act g x)=v.ofLp x}
      one_mem' := by simp
      mul_mem' := by intro g h hg hh x; simpa [map_mul,Equiv.Perm.mul_apply] using (hg (act h x)).trans (hh x)
      inv_mem' := by intro g hg x; simpa using (hg ((act g)⁻¹ x)).symm }
  have hle : Subgroup.closure (⋃ i, (K i : Set G)) ≤ S := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hg
    exact hfix i g hi
  rw [hgen] at hle
  obtain ⟨g,hg⟩ := htrans x y
  exact (hg ▸ (hle (Subgroup.mem_top g) x)).symm

open RubikOBTM.Spectral RubikOBTM.Finite

private theorem RubikOBTM.Spectral.doubled_phase_algebra {G C : Type*} [Group G] (K : Subgroup G) (letter : C → G)
    (hmem : ∀ c, letter c ∈ K) (hrel : RelativeSurjective K letter) (independent : Bool) :
    (∀ c, doubleLetter letter independent c ∈ doubledSubgroup K independent) ∧
    RelativeSurjective (doubledSubgroup K independent) (doubleLetter letter independent) ∧
    ∀ n : K, ((n.val,n.val) : G × G) ∈ doubledSubgroup K independent := by
  cases independent with
  | false =>
    refine ⟨?_,?_,?_⟩
    · intro c
      exact ⟨letter c.1,hmem _,rfl⟩
    · intro g hg
      obtain ⟨u,hu,rfl⟩ := hg
      obtain ⟨c,d,hcd⟩ := hrel u hu
      exact ⟨(c,c),(d,d),by ext <;> simpa [doubleLetter] using hcd⟩
    · intro n
      exact ⟨n.val,n.property,rfl⟩
  | true =>
    refine ⟨?_,?_,?_⟩
    · intro c
      exact ⟨hmem c.1,hmem c.2⟩
    · intro g hg
      obtain ⟨c,d,hcd⟩ := hrel g.1 hg.1
      obtain ⟨e,f,hef⟩ := hrel g.2 hg.2
      exact ⟨(c,e),(d,f),Prod.ext hcd hef⟩
    · intro n
      exact ⟨n.property,n.property⟩

open RubikOBTM.Finite

private theorem RubikOBTM.Finite.doubled_generation_of_normal {H I : Type*} [Group H] (S : I → Subgroup H)
    (hgen : Subgroup.closure (⋃ i, (S i : Set H)) = ⊤)
    (hnormal : ∀ i, Subgroup.normalClosure (S i : Set H) = ⊤)
    (mask : I → Bool) (hmask : ∃ i, mask i = true) :
    Subgroup.closure (⋃ i, (doubledSubgroup (S i) (mask i) : Set (H × H))) = ⊤ := by
  let D := Subgroup.closure (⋃ i, (doubledSubgroup (S i) (mask i) : Set (H × H)))
  let diag : H →* H × H := (MonoidHom.id H).prod (MonoidHom.id H)
  have hdiag : ∀ x : H, diag x ∈ D := by
    have hle : Subgroup.closure (⋃ i, (S i : Set H)) ≤ D.comap diag := by
      apply (Subgroup.closure_le _).mpr
      intro x hx
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
      apply Subgroup.subset_closure
      apply Set.mem_iUnion.mpr
      refine ⟨i,?_⟩
      cases hm : mask i
      · exact ⟨x,hi,rfl⟩
      · exact ⟨hi,hi⟩
    rw [hgen] at hle
    intro x
    exact hle (Subgroup.mem_top x)
  let left : H →* H × H := MonoidHom.inl H H
  let right : H →* H × H := MonoidHom.inr H H
  have hleftNormal : (D.comap left).Normal := by
    constructor
    intro x hx g
    have hh := D.mul_mem (D.mul_mem (hdiag g) hx) (D.inv_mem (hdiag g))
    simpa [diag,left] using hh
  have hrightNormal : (D.comap right).Normal := by
    constructor
    intro x hx g
    have hh := D.mul_mem (D.mul_mem (hdiag g) hx) (D.inv_mem (hdiag g))
    simpa [diag,right] using hh
  obtain ⟨j,hj⟩ := hmask
  letI := hleftNormal
  letI := hrightNormal
  have hleft : Subgroup.normalClosure (S j : Set H) ≤ D.comap left := by
    apply Subgroup.normalClosure_le_normal
    intro x hx
    apply Subgroup.subset_closure
    exact Set.mem_iUnion.mpr ⟨j,by
      simpa [doubledSubgroup,hj,left,Subgroup.mem_prod] using And.intro hx (S j).one_mem⟩
  have hright : Subgroup.normalClosure (S j : Set H) ≤ D.comap right := by
    apply Subgroup.normalClosure_le_normal
    intro x hx
    apply Subgroup.subset_closure
    exact Set.mem_iUnion.mpr ⟨j,by
      simpa [doubledSubgroup,hj,right,Subgroup.mem_prod] using And.intro (S j).one_mem hx⟩
  rw [hnormal j] at hleft hright
  apply top_unique
  intro x hx
  have hl : left x.1 ∈ D := hleft (Subgroup.mem_top _)
  have hr : right x.2 ∈ D := hright (Subgroup.mem_top _)
  simpa [left,right] using D.mul_mem hl hr

open RubikOBTM.Spectral
open scoped Matrix.Norms.L2Operator BigOperators

private theorem RubikOBTM.Spectral.period_contraction {G C X : Type*} [Group G] [Fintype G] [Fintype C] [Nonempty C]
    [Fintype X] [DecidableEq X] [Nonempty X] {T : ℕ}
    (act : G →* Equiv.Perm X) (K : Fin T → Subgroup G) (letter : Fin T → C → G)
    (hmem : ∀ i c, letter i c ∈ K i)
    (hrel : ∀ i, RelativeSurjective (K i) (letter i))
    (hgen : Subgroup.closure (⋃ i, (K i : Set G)) = ⊤)
    (htrans : ∀ x y, ∃ g, act g x = y) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∀ n : ∀ i, K i,
      ‖period (fun i => phaseKernel act (RubikJanson.uniformLaw (inferInstance : Nonempty C))
        (letter i) (n i)) - averaging‖ ≤ θ := by
  classical
  let μ := RubikJanson.uniformLaw (inferInstance : Nonempty C)
  have hμ : ∀ c, 0 < μ.weight c := by
    intro c
    simp only [μ,RubikJanson.uniformLaw]
    positivity
  let q (n : ∀ i, K i) : ℝ := ‖period (fun i => phaseKernel act μ (letter i) (n i)) - averaging‖
  have hq (n : ∀ i, K i) : q n < 1 := by
    apply period_gap_from_rigidity act K hgen htrans
      (fun i => phaseKernel act μ (letter i) (n i))
    · intro i
      exact (phase_norm_rigidity act (K i) μ hμ (letter i) (hmem i) (hrel i) (n i)).1
    · intro i v hv
      have hi := (phase_norm_rigidity act (K i) μ hμ (letter i) (hmem i) (hrel i) (n i)).2 v
      exact ⟨hi.1.mp hv,hi.2 (hi.1.mp hv)⟩
  obtain ⟨n,hn⟩ := Finite.exists_max q
  refine ⟨(q n+1)/2,?_,by linarith [hq n],?_⟩
  · have hpos : 0 ≤ q n := norm_nonneg _
    linarith
  · intro m
    exact (hn m).trans (by linarith [hq n])

open RubikOBTM.Spectral
open scoped Matrix.Norms.L2Operator BigOperators

private theorem RubikOBTM.Spectral.doubled_period_contraction {G C X : Type*} [Group G] [Fintype G] [Fintype C] [Nonempty C]
    [Fintype X] [DecidableEq X] [Nonempty X] {T : ℕ} (hT : 0 < T)
    (act : G →* Equiv.Perm X) (K : Fin T → Subgroup G) (letter : Fin T → C → G)
    (hmem : ∀ i c, letter i c ∈ K i)
    (hrel : ∀ i, RelativeSurjective (K i) (letter i))
    (hgen : Subgroup.closure (⋃ i, (K i : Set G)) = ⊤)
    (hnormal : ∀ i, Subgroup.normalClosure (K i : Set G) = ⊤)
    (htrans : ∀ x y, ∃ g, act g x = y) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∀ (n : ∀ i, K i) (independent : Fin T → Bool),
      (∃ i, independent i = true) →
      ‖period (fun i => phaseKernel (pairAction act)
        (RubikJanson.uniformLaw (inferInstance : Nonempty (C × C)))
        (doubleLetter (letter i) (independent i)) ((n i).val,(n i).val)) - averaging‖ ≤ η := by
  classical
  let μ := RubikJanson.uniformLaw (inferInstance : Nonempty (C × C))
  have hμ : ∀ c, 0 < μ.weight c := by
    intro c
    simp only [μ,RubikJanson.uniformLaw]
    positivity
  have ht : ∀ x y : X × X, ∃ g, pairAction act g x = y := by
    intro x y
    obtain ⟨g,hg⟩ := htrans x.1 y.1
    obtain ⟨h,hh⟩ := htrans x.2 y.2
    exact ⟨(g,h),Prod.ext hg hh⟩
  let Masks := {b : Fin T → Bool // ∃ i, b i = true}
  haveI : Nonempty Masks := ⟨⟨fun _ => true,⟨⟨0,hT⟩,rfl⟩⟩⟩
  let q (p : Masks × (∀ i, K i)) : ℝ :=
    ‖period (fun i => phaseKernel (pairAction act) μ
      (doubleLetter (letter i) (p.1.val i)) ((p.2 i).val,(p.2 i).val)) - averaging‖
  have hq (p : Masks × (∀ i, K i)) : q p < 1 := by
    let H (i : Fin T) := RubikOBTM.Finite.doubledSubgroup (K i) (p.1.val i)
    have hp i := doubled_phase_algebra (K i) (letter i) (hmem i) (hrel i) (p.1.val i)
    let n' (i : Fin T) : H i := ⟨((p.2 i).val,(p.2 i).val),hp i |>.2.2 (p.2 i)⟩
    have hg := RubikOBTM.Finite.doubled_generation_of_normal K hgen hnormal p.1.val p.1.property
    apply period_gap_from_rigidity (pairAction act) H hg ht
      (fun i => phaseKernel (pairAction act) μ (doubleLetter (letter i) (p.1.val i)) (n' i))
    · intro i
      exact (phase_norm_rigidity (pairAction act) (H i) μ hμ _ (hp i).1 (hp i).2.1 (n' i)).1
    · intro i v hv
      have hi := (phase_norm_rigidity (pairAction act) (H i) μ hμ _ (hp i).1 (hp i).2.1 (n' i)).2 v
      exact ⟨hi.1.mp hv,hi.2 (hi.1.mp hv)⟩
  obtain ⟨p,hp⟩ := Finite.exists_max q
  refine ⟨(q p+1)/2,?_,by linarith [hq p],?_⟩
  · have hpos : 0 ≤ q p := norm_nonneg _
    linarith
  · intro n b hb
    exact (hp (⟨b,hb⟩,n)).trans (by linarith [hq p])

open scoped Matrix.Norms.L2Operator BigOperators Classical
open RubikOBTM.Spectral

set_option maxRecDepth 2048 in
theorem proof_RubikOBTM_Spectral_actual_period_gaps : ∃ θ η : ℝ, 0 < θ ∧ θ < 1 ∧ 0 < η ∧ η < 1 ∧
    (∀ n : Fin RubikOBTM.Finite.period → RubikOBTM.Finite.Intrinsic,
      ‖singleWordMatrix actualPeriodPositive RubikOBTM.Finite.nativeC actualAlphabetNonempty
        RubikOBTM.Finite.periodicAct n - averaging‖ ≤ θ) ∧
    (∀ (n : Fin RubikOBTM.Finite.period → RubikOBTM.Finite.Intrinsic)
      (shared : Fin RubikOBTM.Finite.period → Bool), (∃ i, shared i = false) →
      ‖doubleWordMatrix actualPeriodPositive RubikOBTM.Finite.nativeC actualAlphabetNonempty
        RubikOBTM.Finite.periodicAct n shared - averaging‖ ≤ η) := by
  classical
  letI : DecidableEq (RubikOBTM.Finite.Z × RubikOBTM.Finite.Z) := instDecidableEqProd
  let KF (i : Fin RubikOBTM.Finite.period) := RubikOBTM.Finite.K (RubikOBTM.Finite.phaseAt i)
  let letters (i : Fin RubikOBTM.Finite.period) := RubikOBTM.Finite.letter (RubikOBTM.Finite.phaseAt i)
  have hm : ∀ i c, letters i c ∈ KF i := fun i c => (RubikOBTM.Finite.subgroupLetter _ c).property
  have hr : ∀ i, RelativeSurjective (KF i) (letters i) := fun i => RubikOBTM.Finite.relative_surjective _
  have hg : Subgroup.closure (⋃ i, (KF i : Set RubikOBTM.Finite.G)) = ⊤ := by
    have he : (⋃ i, (KF i : Set RubikOBTM.Finite.G)) =
        ⋃ j : RubikOBTM.Finite.Phase, (RubikOBTM.Finite.K j : Set RubikOBTM.Finite.G) := by
      ext g
      simp only [Set.mem_iUnion]
      constructor
      · rintro ⟨i,hi⟩
        exact ⟨RubikOBTM.Finite.phaseAt i,hi⟩
      · rintro ⟨j,hj⟩
        exact ⟨RubikOBTM.Finite.phaseIndex j,by simpa [KF,RubikOBTM.Finite.phaseAt] using hj⟩
    rw [he]
    exact RubikOBTM.Finite.union_generation
  obtain ⟨θ,hθ0,hθ1,hθ⟩ := period_contraction RubikOBTM.Finite.act KF letters hm hr hg
    RubikOBTM.Finite.transitive
  obtain ⟨η,hη0,hη1,hη⟩ := doubled_period_contraction actualPeriodPositive RubikOBTM.Finite.act
    KF letters hm hr hg (fun i => RubikOBTM.Finite.normal_K _) RubikOBTM.Finite.transitive
  have hp (i : Fin RubikOBTM.Finite.period) :
      RubikOBTM.Periodic.phase _ actualPeriodPositive i = i :=
    Fin.ext (Nat.mod_eq_of_lt i.isLt)
  let native := RubikOBTM.Periodic.NativeConstant RubikOBTM.Finite.nativeC
  haveI : Nonempty native := actualAlphabetNonempty.to_subtype
  have htransport (D E Y : Type) [Fintype D] [Fintype E] [Fintype Y] [Nonempty D] [Nonempty E]
      (e : D ≃ E) (f : E → Equiv.Perm Y) :
      RubikChannel.transition (RubikJanson.uniformLaw (inferInstance : Nonempty D)) (fun d => f (e d)) =
      RubikChannel.transition (RubikJanson.uniformLaw (inferInstance : Nonempty E)) f := by
    ext x y
    change (∑ d, (1 / (Fintype.card D : ℝ)) * RubikChannel.rowPermutation (f (e d)) x y) =
      ∑ e, (1 / (Fintype.card E : ℝ)) * RubikChannel.rowPermutation (f e) x y
    rw [Fintype.card_congr e]
    exact e.sum_comp (fun z => (1 / (Fintype.card E : ℝ)) * RubikChannel.rowPermutation (f z) x y)
  let np (n : Fin RubikOBTM.Finite.period → RubikOBTM.Finite.Intrinsic) (i : Fin RubikOBTM.Finite.period) : KF i :=
    ⟨RubikOBTM.Finite.phaseHom (RubikOBTM.Finite.phaseAt i) (n i),⟨⟨(n i).1,rfl⟩,⟨(n i).2,rfl⟩⟩⟩
  have word_period {D Y : Type} [Fintype D] [Fintype Y] [d : DecidableEq Y]
      (μ : RubikJanson.FiniteLaw D) {l : ℕ} (a : Fin l → D → Equiv.Perm Y) :
      RubikChannel.wordMatrix μ a = RubikOBTM.Spectral.period (fun i => RubikChannel.transition μ (a i)) := by
    have he : d = Classical.decEq Y := Subsingleton.elim _ _
    cases he
    rfl
  have hs n : singleWordMatrix actualPeriodPositive RubikOBTM.Finite.nativeC actualAlphabetNonempty
      RubikOBTM.Finite.periodicAct n = RubikOBTM.Spectral.period (fun i => phaseKernel RubikOBTM.Finite.act
        (RubikJanson.uniformLaw (inferInstance : Nonempty RubikOBTM.Finite.Native)) (letters i) (np n i)) := by
    unfold singleWordMatrix RubikChannel.wordMatrix RubikOBTM.Spectral.period
    apply congrArg List.prod
    apply congrArg List.ofFn
    funext i
    simp only [hp]
    have ht := htransport RubikOBTM.Finite.Native native RubikOBTM.Finite.Z RubikOBTM.Finite.nativeEquiv
      (fun c => RubikOBTM.Finite.periodicAct i (n i * c.val))
    convert ht.symm using 1
    funext c
    simp [phaseKernel,np,letters,RubikOBTM.Finite.periodicAct,RubikOBTM.Finite.phaseAct,
      RubikOBTM.Finite.phaseHom,RubikOBTM.Finite.letter,RubikOBTM.Finite.nativeEquiv,map_mul]
  have hd n shared : doubleWordMatrix actualPeriodPositive RubikOBTM.Finite.nativeC actualAlphabetNonempty
      RubikOBTM.Finite.periodicAct n shared = RubikOBTM.Spectral.period (fun i => phaseKernel (pairAction RubikOBTM.Finite.act)
        (RubikJanson.uniformLaw (inferInstance : Nonempty (RubikOBTM.Finite.Native × RubikOBTM.Finite.Native)))
        (doubleLetter (letters i) (!(shared i))) ((np n i).val,(np n i).val)) := by
    unfold doubleWordMatrix
    rw [word_period]
    unfold RubikOBTM.Spectral.period
    apply congrArg List.prod
    apply congrArg List.ofFn
    funext i
    simp only [hp]
    have ht := htransport (RubikOBTM.Finite.Native × RubikOBTM.Finite.Native) (native × native)
      (RubikOBTM.Finite.Z × RubikOBTM.Finite.Z)
      (RubikOBTM.Finite.nativeEquiv.prodCongr RubikOBTM.Finite.nativeEquiv)
      (fun c => (RubikOBTM.Finite.periodicAct i (n i * c.1.val)).prodCongr
        (RubikOBTM.Finite.periodicAct i (n i * (if shared i then c.1 else c.2).val)))
    convert ht.symm using 1
    funext c
    cases hb : shared i <;>
      simp [phaseKernel,np,letters,RubikOBTM.Finite.periodicAct,RubikOBTM.Finite.phaseAct,
        RubikOBTM.Finite.phaseHom,RubikOBTM.Finite.letter,RubikOBTM.Finite.nativeEquiv,
        doubleLetter,pairAction,hb,map_mul]
  refine ⟨θ,η,hθ0,hθ1,hη0,hη1,?_,?_⟩
  · intro n
    rw [hs]
    exact hθ (np n)
  · intro n shared hshared
    rw [hd]
    apply hη (np n) (fun i => !(shared i))
    obtain ⟨i,hi⟩ := hshared
    exact ⟨i,by simp [hi]⟩
