import RubikSTM.Definitions.OBTM.Spectral.SingleWordMatrix
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
open scoped Classical BigOperators

private theorem RubikChannel.word_expect_succ {C : Type*} [Fintype C]
    (μ : RubikJanson.FiniteLaw C)
    (L : ℕ) (f : (Fin (L + 1) → C) → ℝ) :
    (RubikChannel.wordLaw μ (L + 1)).expect f =
      ∑ c, μ.weight c * (RubikChannel.wordLaw μ L).expect
        (fun w => f (Fin.cons c w)) := by
  classical
  unfold RubikJanson.FiniteLaw.expect
  change (∑ w : Fin (L + 1) → C, (∏ i, μ.weight (w i)) * f w) =
    ∑ c, μ.weight c * ∑ w : Fin L → C, (∏ i, μ.weight (w i)) * f (Fin.cons c w)
  rw [← (Fin.consEquiv (fun _ : Fin (L + 1) => C)).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  simp only [Finset.mul_sum, mul_assoc]
  rfl

private theorem RubikChannel.transition_mul_entry {C X : Type*} [Fintype C] [Fintype X]
    [DecidableEq X]
    (μ : RubikJanson.FiniteLaw C) (act : C → Equiv.Perm X)
    (A : Matrix X X ℝ) (x y : X) :
    (RubikChannel.transition μ act * A) x y =
      ∑ c, μ.weight c * A (act c x) y := by
  classical
  simp only [Matrix.mul_apply, RubikChannel.transition, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  simp [RubikChannel.rowPermutation, mul_ite, ite_mul, eq_comm]

private theorem RubikChannel.run_marginal {C X : Type*} [Fintype C] [Fintype X] [DecidableEq X]
    (μ : RubikJanson.FiniteLaw C) (L : ℕ)
    (act : Fin L → C → Equiv.Perm X) (x y : X) :
    (RubikChannel.wordLaw μ L).prob (fun w => RubikChannel.run act w x = y) =
      RubikChannel.wordMatrix μ act x y := by
  classical
  induction L generalizing x with
  | zero =>
      simp [RubikJanson.FiniteLaw.prob, RubikJanson.FiniteLaw.expect,
        RubikChannel.wordLaw, RubikChannel.run, RubikChannel.wordMatrix, Matrix.one_apply]
  | succ L ih =>
      have hr (c : C) (w : Fin L → C) :
          RubikChannel.run act (Fin.cons c w) x =
            RubikChannel.run (fun i => act i.succ) w (act 0 c x) := by
        simp [RubikChannel.run, List.ofFn_succ]
      unfold RubikJanson.FiniteLaw.prob
      rw [RubikChannel.word_expect_succ]
      simp_rw [hr]
      calc
        _ = ∑ c, μ.weight c * RubikChannel.wordMatrix μ
            (fun i => act i.succ) (act 0 c x) y := by
          apply Finset.sum_congr rfl
          intro c _
          apply congrArg (fun z : ℝ => μ.weight c * z)
          refine Eq.trans ?_ (ih (fun i => act i.succ) (act 0 c x))
          unfold RubikJanson.FiniteLaw.prob
          apply congrArg (RubikChannel.wordLaw μ L).expect
          funext w
          by_cases h : RubikChannel.run (fun i => act i.succ) w (act 0 c x) = y
          · simp only [h, if_true]
          · simp only [h, if_false]
        _ = _ := by
          simpa only [RubikChannel.wordMatrix, List.ofFn_succ, List.prod_cons] using
            (RubikChannel.transition_mul_entry μ (act 0)
              (RubikChannel.wordMatrix μ (fun i => act i.succ)) x y).symm

open RubikOBTM.Periodic RubikOBTM.Spectral

private theorem RubikOBTM.Spectral.LongWord.prob_entry {T : ℕ} {K Z : Type*} [Group K] [Fintype Z] [DecidableEq Z]
    (hT : 0 < T) (C : Finset K) (hC : C.Nonempty)
    (act : Fin T → K →* Equiv.Perm Z) {L : ℕ} (n : Fin L → K) (x y : Z) :
    coordinateProb hT C hC act n x y = singleWordMatrix hT C hC act n x y := by
  classical
  haveI : Nonempty (NativeConstant C) := hC.to_subtype
  let μ := RubikJanson.uniformLaw (inferInstance : Nonempty (NativeConstant C))
  have hu (f : (Fin L → NativeConstant C) → ℝ) :
      (RubikJanson.uniformLaw (inferInstance : Nonempty (Fin L → NativeConstant C))).expect f =
        (RubikChannel.wordLaw μ L).expect f := by
    unfold RubikJanson.FiniteLaw.expect
    apply Finset.sum_congr rfl
    intro w _
    simp [μ,RubikJanson.uniformLaw,RubikChannel.wordLaw,Fintype.card_fun,div_pow]
  unfold coordinateProb RubikJanson.FiniteLaw.prob
  rw [hu]
  exact RubikChannel.run_marginal μ L
    (fun i c => act (phase T hT i) (n i * c.val)) x y

private theorem RubikOBTM.Spectral.LongWord.joint_entry {T : ℕ} {K Z : Type*} [Group K] [Fintype Z] [DecidableEq Z]
    (hT : 0 < T) (C : Finset K) (hC : C.Nonempty)
    (act : Fin T → K →* Equiv.Perm Z) {L : ℕ}
    (n : Fin L → K) (shared : Fin L → Bool) (x y : Z) :
    coordinateJointProb hT C hC act n shared x y =
      doubleWordMatrix hT C hC act n shared (x,x) (y,y) := by
  classical
  haveI : Nonempty (NativeConstant C) := hC.to_subtype
  let D := NativeConstant C × NativeConstant C
  let μ := RubikJanson.uniformLaw (inferInstance : Nonempty D)
  have hu (f : (Fin L → D) → ℝ) :
      (RubikJanson.uniformLaw (inferInstance : Nonempty (Fin L → D))).expect f =
        (RubikChannel.wordLaw μ L).expect f := by
    unfold RubikJanson.FiniteLaw.expect
    apply Finset.sum_congr rfl
    intro w _
    simp [μ,RubikJanson.uniformLaw,RubikChannel.wordLaw,Fintype.card_fun,div_pow]
  have hr : ∀ {l : ℕ} (a b : Fin l → D → Equiv.Perm Z) (w : Fin l → D) (u v : Z),
      RubikChannel.run (fun i c => (a i c).prodCongr (b i c)) w (u,v) =
        (RubikChannel.run a w u,RubikChannel.run b w v) := by
    intro l
    induction l with
    | zero => intros; simp [RubikChannel.run]
    | succ l ih =>
      intro a b w u v
      simpa only [RubikChannel.run,List.ofFn_succ,List.foldl_cons,Equiv.prodCongr_apply,
        Prod.map_apply] using
        ih (fun i => a i.succ) (fun i => b i.succ) (fun i => w i.succ)
          (a 0 (w 0) u) (b 0 (w 0) v)
  unfold coordinateJointProb RubikJanson.FiniteLaw.prob
  rw [hu]
  have hm := RubikChannel.run_marginal μ L
    (fun i c => (act (phase T hT i) (n i * c.1.val)).prodCongr
      (act (phase T hT i) (n i * (if shared i then c.1 else c.2).val))) (x,x) (y,y)
  calc
    _ = (RubikChannel.wordLaw μ L).prob (fun w => RubikChannel.run
        (fun i c => (act (phase T hT i) (n i * c.1.val)).prodCongr
          (act (phase T hT i) (n i * (if shared i then c.1 else c.2).val))) w (x,x) = (y,y)) := by
      unfold RubikJanson.FiniteLaw.prob
      apply congrArg (RubikChannel.wordLaw μ L).expect
      funext w
      dsimp only
      simp only [hr (fun i c => act (phase T hT i) (n i * c.1.val))
        (fun i c => act (phase T hT i) (n i * (if shared i then c.1 else c.2).val)) w x x,
        Prod.mk.injEq]
      simp only [coordinateRun,RubikChannel.run]
      split_ifs <;> simp_all
    _ = _ := hm

private theorem RubikOBTM.Spectral.LongWord.transition_stochastic {C X : Type*} [Fintype C] [Fintype X] [DecidableEq X]
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

private theorem RubikOBTM.Spectral.LongWord.stochastic_residual_norm_le_one {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] (P : Matrix n n ℝ) (hP : P ∈ doublyStochastic ℝ n) :
    let J : Matrix n n ℝ := fun _ _ => (Fintype.card n : ℝ)⁻¹
    ‖P - J‖ ≤ 1 := by
  let J : Matrix n n ℝ := fun _ _ => (Fintype.card n : ℝ)⁻¹
  change ‖P - J‖ ≤ 1
  have hc : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hPJ : P * J = J := by
    ext i j
    change (∑ k, P i k * (Fintype.card n : ℝ)⁻¹) = _
    rw [← Finset.sum_mul, sum_row_of_mem_doublyStochastic hP i, one_mul]
  have hJJ : J * J = J := by
    ext i j
    change (∑ _ : n, (Fintype.card n : ℝ)⁻¹ * (Fintype.card n : ℝ)⁻¹) = (Fintype.card n : ℝ)⁻¹
    simp [hc]
  have hstar : star J = J := by
    ext i j
    change star (J j i) = J i j
    simp [J]
  have hproj : IsStarProjection J := ⟨hJJ, hstar⟩
  have hres : P - J = P * (1 - J) := by rw [mul_sub, mul_one, hPJ]
  rw [hres]
  calc
    ‖P * (1 - J)‖ ≤ ‖P‖ * ‖1 - J‖ := norm_mul_le _ _
    _ ≤ 1 * 1 := mul_le_mul (Matrix.l2_opNorm_le_one_of_mem_doublyStochastic hP)
      (IsStarProjection.norm_le _ hproj.one_sub) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

open scoped Matrix in

private theorem RubikOBTM.Spectral.LongWord.entry_norm_le {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace ℝ n := EuclideanSpace.single j 1
  have he : (Matrix.toEuclideanCLM (𝕜 := ℝ) A e) i = A i j := by
    change (A *ᵥ Pi.single j 1) i = A i j
    rw [Matrix.mulVec_single_one]
    rfl
  calc
    ‖A i j‖ = ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) A e) i‖ := congrArg norm he.symm
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A e‖ := PiLp.norm_apply_le _ i
    _ ≤ ‖A‖ * ‖e‖ := (Matrix.toEuclideanCLM (𝕜 := ℝ) A).le_opNorm e
    _ = ‖A‖ := by simp [e]

private theorem RubikOBTM.Spectral.LongWord.wordMatrix_mem {C X : Type*} [Fintype C] [Fintype X]
    (μ : RubikJanson.FiniteLaw C) {L : ℕ} (f : Fin L → C → Equiv.Perm X) :
    RubikChannel.wordMatrix μ f ∈ doublyStochastic ℝ X := by
  unfold RubikChannel.wordMatrix
  apply Submonoid.list_prod_mem
  intro P hP
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hP
  exact transition_stochastic μ (f i)

private theorem RubikOBTM.Spectral.LongWord.mul_averaging {X : Type*} [Fintype X] {P : Matrix X X ℝ}
    (hP : P ∈ doublyStochastic ℝ X) :
    P * (averaging : Matrix X X ℝ) = averaging := by
  ext i j
  simp only [Matrix.mul_apply, averaging]
  rw [← Finset.sum_mul, sum_row_of_mem_doublyStochastic hP i, one_mul]

private theorem RubikOBTM.Spectral.LongWord.averaging_mul {X : Type*} [Fintype X] {P : Matrix X X ℝ}
    (hP : P ∈ doublyStochastic ℝ X) :
    (averaging : Matrix X X ℝ) * P = averaging := by
  ext i j
  simp only [Matrix.mul_apply, averaging]
  rw [← Finset.mul_sum, sum_col_of_mem_doublyStochastic hP j, mul_one]

private theorem RubikOBTM.Spectral.LongWord.averaging_mul_self {X : Type*} [Fintype X] [Nonempty X] :
    (averaging : Matrix X X ℝ) * averaging = averaging := by
  have hc : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  ext i j
  simp only [Matrix.mul_apply, averaging, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]

private theorem RubikOBTM.Spectral.LongWord.residual_mul {X : Type*} [Fintype X] [Nonempty X] (A B : Matrix X X ℝ)
    (hA : A * (averaging : Matrix X X ℝ) = averaging)
    (hB : (averaging : Matrix X X ℝ) * B = averaging) :
    A * B - averaging = (A - averaging) * (B - averaging) := by
  rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hA, hB, averaging_mul_self,
    sub_self, sub_zero]

private theorem RubikOBTM.Spectral.LongWord.wordMatrix_residual_le {C X : Type*} [Fintype C] [Fintype X] [Nonempty X]
    (μ : RubikJanson.FiniteLaw C) {L : ℕ} (f : Fin L → C → Equiv.Perm X) :
    ‖RubikChannel.wordMatrix μ f - averaging‖ ≤ 1 :=
  stochastic_residual_norm_le_one _ (wordMatrix_mem μ f)

private theorem RubikOBTM.Spectral.LongWord.wordMatrix_append {C X : Type*} [Fintype C] [Fintype X]
    (μ : RubikJanson.FiniteLaw C) {a b : ℕ} (f : Fin (a + b) → C → Equiv.Perm X) :
    RubikChannel.wordMatrix μ f =
      RubikChannel.wordMatrix μ (fun i => f (Fin.castAdd b i)) *
        RubikChannel.wordMatrix μ (fun j => f (Fin.natAdd a j)) := by
  simp only [RubikChannel.wordMatrix, List.ofFn_add, List.prod_append]
  rfl

private theorem RubikOBTM.Spectral.LongWord.phase_castAdd {T : ℕ} (hT : 0 < T) {a : ℕ} (i : Fin a) :
    phase T hT (Fin.castAdd T i) = phase T hT i := rfl

private theorem RubikOBTM.Spectral.LongWord.phase_natAdd {T : ℕ} (hT : 0 < T) (m : ℕ) (j : Fin T) :
    phase T hT (Fin.natAdd (T * m) j) = phase T hT j := by
  apply Fin.ext
  show (T * m + j.val) % T = j.val % T
  rw [Nat.mul_add_mod]

private theorem RubikOBTM.Spectral.LongWord.single_append {T : ℕ} {K Z : Type*} [Group K] [Fintype Z]
    (hT : 0 < T) (C : Finset K) (hC : C.Nonempty) (act : Fin T → K →* Equiv.Perm Z)
    (m : ℕ) (n : Fin (T * m + T) → K) :
    singleWordMatrix hT C hC act n =
      singleWordMatrix hT C hC act (fun i : Fin (T * m) => n (Fin.castAdd T i)) *
        singleWordMatrix hT C hC act (fun j : Fin T => n (Fin.natAdd (T * m) j)) := by
  simp only [singleWordMatrix]
  rw [wordMatrix_append (a := T * m) (b := T)]
  simp only [phase_castAdd, phase_natAdd]

private theorem RubikOBTM.Spectral.LongWord.double_append {T : ℕ} {K Z : Type*} [Group K] [Fintype Z]
    (hT : 0 < T) (C : Finset K) (hC : C.Nonempty) (act : Fin T → K →* Equiv.Perm Z)
    (m : ℕ) (n : Fin (T * m + T) → K) (shared : Fin (T * m + T) → Bool) :
    doubleWordMatrix hT C hC act n shared =
      doubleWordMatrix hT C hC act (fun i : Fin (T * m) => n (Fin.castAdd T i))
          (fun i => shared (Fin.castAdd T i)) *
        doubleWordMatrix hT C hC act (fun j : Fin T => n (Fin.natAdd (T * m) j))
          (fun j => shared (Fin.natAdd (T * m) j)) := by
  simp only [doubleWordMatrix]
  rw [wordMatrix_append (a := T * m) (b := T)]
  simp only [phase_castAdd, phase_natAdd]

private theorem RubikOBTM.Spectral.LongWord.single_mem {T : ℕ} {K Z : Type*} [Group K] [Fintype Z]
    (hT : 0 < T) (C : Finset K) (hC : C.Nonempty) (act : Fin T → K →* Equiv.Perm Z)
    {L : ℕ} (n : Fin L → K) :
    singleWordMatrix hT C hC act n ∈ doublyStochastic ℝ Z :=
  wordMatrix_mem _ _

private theorem RubikOBTM.Spectral.LongWord.double_mem {T : ℕ} {K Z : Type*} [Group K] [Fintype Z]
    (hT : 0 < T) (C : Finset K) (hC : C.Nonempty) (act : Fin T → K →* Equiv.Perm Z)
    {L : ℕ} (n : Fin L → K) (shared : Fin L → Bool) :
    doubleWordMatrix hT C hC act n shared ∈ doublyStochastic ℝ (Z × Z) :=
  wordMatrix_mem _ _

private theorem RubikOBTM.Spectral.LongWord.card_false_add {a b : ℕ} (s : Fin (a + b) → Bool) :
    (Finset.univ.filter (fun i => s i = false)).card =
      (Finset.univ.filter (fun i : Fin a => s (Fin.castAdd b i) = false)).card +
        (Finset.univ.filter (fun j : Fin b => s (Fin.natAdd a j) = false)).card := by
  simp only [Finset.card_filter]
  exact Fin.sum_univ_add (fun i => if s i = false then 1 else 0)

private theorem RubikOBTM.Spectral.LongWord.single_norm {T : ℕ} {K Z : Type*} [Group K] [Fintype Z] [Nonempty Z]
    (hT : 0 < T) (C : Finset K) (hC : C.Nonempty) (act : Fin T → K →* Equiv.Perm Z)
    (θ : ℝ) (hθ0 : 0 ≤ θ)
    (hsingle : ∀ n : Fin T → K,
      ‖singleWordMatrix hT C hC act n - averaging‖ ≤ θ) :
    ∀ (m : ℕ) (n : Fin (T * m) → K),
      ‖singleWordMatrix hT C hC act n - averaging‖ ≤ θ ^ m := by
  intro m
  induction m with
  | zero =>
      intro n
      rw [pow_zero]
      exact wordMatrix_residual_le _ _
  | succ m ih =>
      show ∀ n : Fin (T * m + T) → K,
        ‖singleWordMatrix hT C hC act n - averaging‖ ≤ θ ^ (m + 1)
      intro n
      rw [single_append hT C hC act m n,
        residual_mul _ _ (mul_averaging (single_mem hT C hC act _))
          (averaging_mul (single_mem hT C hC act _)), pow_succ]
      exact (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul (ih _) (hsingle _) (norm_nonneg _) (pow_nonneg hθ0 _))

private theorem RubikOBTM.Spectral.LongWord.double_norm {T : ℕ} {K Z : Type*} [Group K] [Fintype Z] [Nonempty Z]
    (hT : 0 < T) (C : Finset K) (hC : C.Nonempty) (act : Fin T → K →* Equiv.Perm Z)
    (η ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hηρ : η ≤ ρ ^ T)
    (hdouble : ∀ (n : Fin T → K) (shared : Fin T → Bool), (∃ i, shared i = false) →
      ‖doubleWordMatrix hT C hC act n shared - averaging‖ ≤ η) :
    ∀ (m : ℕ) (n : Fin (T * m) → K) (shared : Fin (T * m) → Bool),
      ‖doubleWordMatrix hT C hC act n shared - averaging‖ ≤
        ρ ^ (Finset.univ.filter (fun i => shared i = false)).card := by
  intro m
  induction m with
  | zero =>
      intro n shared
      have h0 : (Finset.univ.filter (fun i : Fin (T * 0) => shared i = false)).card = 0 := by
        simp
      rw [h0, pow_zero]
      exact wordMatrix_residual_le _ _
  | succ m ih =>
      show ∀ (n : Fin (T * m + T) → K) (shared : Fin (T * m + T) → Bool),
        ‖doubleWordMatrix hT C hC act n shared - averaging‖ ≤
          ρ ^ (Finset.univ.filter (fun i => shared i = false)).card
      intro n shared
      rw [double_append hT C hC act m n shared,
        residual_mul _ _ (mul_averaging (double_mem hT C hC act _ _))
          (averaging_mul (double_mem hT C hC act _ _)),
        card_false_add shared, pow_add]
      refine (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul (ih _ _) ?_ (norm_nonneg _) (pow_nonneg hρ0 _))
      by_cases hb : ∃ j : Fin T, shared (Fin.natAdd (T * m) j) = false
      · have hcard : (Finset.univ.filter
            (fun j : Fin T => shared (Fin.natAdd (T * m) j) = false)).card ≤ T := by
          simpa using Finset.card_filter_le (Finset.univ : Finset (Fin T))
            (fun j : Fin T => shared (Fin.natAdd (T * m) j) = false)
        exact (hdouble _ _ hb).trans (hηρ.trans (pow_le_pow_of_le_one hρ0 hρ1 hcard))
      · push Not at hb
        have h0 : (Finset.univ.filter
            (fun j : Fin T => shared (Fin.natAdd (T * m) j) = false)).card = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro j _
          simp [hb j]
        rw [h0, pow_zero]
        exact wordMatrix_residual_le _ _

private theorem RubikOBTM.Spectral.LongWord.rate_choice {T : ℕ} (hT : 0 < T) (η : ℝ) (hη0 : 0 < η) (hη1 : η < 1) :
    0 < 1 - (1 - η) / T ∧ 1 - (1 - η) / T < 1 ∧ η ≤ (1 - (1 - η) / T) ^ T := by
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hd : (1 - η) / T ≤ 1 - η := div_le_self (by linarith) hT1
  have hd0 : 0 < (1 - η) / T := div_pos (by linarith) hTpos
  refine ⟨by linarith, by linarith, ?_⟩
  have hb := one_add_mul_le_pow (a := -((1 - η) / T)) (by linarith) T
  have hTm : (T : ℝ) * -((1 - η) / T) = -(1 - η) := by
    field_simp
  rw [hTm] at hb
  have hρ : (1 : ℝ) + -((1 - η) / T) = 1 - (1 - η) / T := by ring
  rw [hρ] at hb
  linarith

open RubikOBTM.Periodic RubikOBTM.Spectral RubikOBTM.Spectral.LongWord in
theorem proof_RubikOBTM_Spectral_coordinate_bounds_of_period_gaps {T : ℕ} {K Z : Type*} [Group K] [Fintype Z] [dZ : DecidableEq Z] [Nonempty Z]
    (hT : 0 < T) (C : Finset K) (hC : C.Nonempty) (act : Fin T → K →* Equiv.Perm Z)
    (θ η : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hη0 : 0 < η) (hη1 : η < 1)
    (hsingle : ∀ n : Fin T → K,
      ‖RubikOBTM.Spectral.singleWordMatrix hT C hC act n - RubikOBTM.Spectral.averaging‖ ≤ θ)
    (hdouble : ∀ (n : Fin T → K) (shared : Fin T → Bool), (∃ i, shared i = false) →
      ‖RubikOBTM.Spectral.doubleWordMatrix hT C hC act n shared - RubikOBTM.Spectral.averaging‖ ≤ η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ RubikOBTM.Periodic.CoordinateBounds hT C hC act θ ρ := by
  obtain rfl : dZ = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  obtain ⟨hρ0, hρ1, hηρ⟩ := rate_choice hT η hη0 hη1
  refine ⟨1 - (1 - η) / T, hρ0, hρ1, ?_⟩
  intro L _ hTL n x y
  obtain ⟨m, rfl⟩ := hTL
  have hq : (0 : ℝ) < Fintype.card Z := by exact_mod_cast Fintype.card_pos
  refine ⟨?_, ?_⟩
  ·
    rw [prob_entry]
    have hn := single_norm hT C hC act θ hθ0.le hsingle m n
    have he := entry_norm_le (singleWordMatrix hT C hC act n - averaging) x y
    have hentry : (singleWordMatrix hT C hC act n - averaging : Matrix Z Z ℝ) x y =
        singleWordMatrix hT C hC act n x y - (Fintype.card Z : ℝ)⁻¹ := rfl
    rw [hentry, Real.norm_eq_abs] at he
    have habs := (abs_le.mp (he.trans hn)).1
    unfold lowerEnvelope
    rw [Nat.mul_div_cancel_left m hT, one_div]
    linarith
  ·
    intro shared
    rw [joint_entry]
    have hn := double_norm hT C hC act η (1 - (1 - η) / T) hρ0.le hρ1.le hηρ hdouble m n shared
    have he := entry_norm_le (doubleWordMatrix hT C hC act n shared - averaging) (x, x) (y, y)
    have hentry :
        (doubleWordMatrix hT C hC act n shared - averaging : Matrix (Z × Z) (Z × Z) ℝ)
          (x, x) (y, y) =
        doubleWordMatrix hT C hC act n shared (x, x) (y, y) -
          (Fintype.card (Z × Z) : ℝ)⁻¹ := rfl
    rw [hentry, Real.norm_eq_abs] at he
    have habs := (abs_le.mp (he.trans hn)).2
    have hcard : (Fintype.card (Z × Z) : ℝ)⁻¹ = 1 / (Fintype.card Z : ℝ) ^ 2 := by
      rw [Fintype.card_prod, Nat.cast_mul, one_div, sq]
    rw [hcard] at habs
    linarith
