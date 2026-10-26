import RubikSTM.Definitions.OBTM.Band.Finite.ModelEval
import Mathlib.Tactic
set_option autoImplicit false
open RubikOBTM.Band RubikOBTM.Band.Finite Equiv.Perm
open scoped Classical

private theorem RubikOBTM.Band.Finite.kernel_diagonal (r u v : RubikOBTM.Band.Perm) :
  RubikOBTM.Band.Finite.kernel (r * u, r * v) =
    (r,r) * RubikOBTM.Band.Finite.kernel (u,v) * (r,r)⁻¹ := by
  apply Prod.ext
  · change (r*u)*actualSlabPlus*(r*u)⁻¹ * ((r*v)*actualSlabPlus*(r*v)⁻¹)⁻¹ =
      r * (u*actualSlabPlus*u⁻¹ * (v*actualSlabPlus*v⁻¹)⁻¹) * r⁻¹
    group
  · change (r*u)*actualSlabMinus*(r*u)⁻¹ * ((r*v)*actualSlabMinus*(r*v)⁻¹)⁻¹ =
      r * (u*actualSlabMinus*u⁻¹ * (v*actualSlabMinus*v⁻¹)⁻¹) * r⁻¹
    group

private theorem RubikOBTM.Band.Finite.kernel_seeds :
  RubikOBTM.Band.Finite.kernel (Equiv.swap 2 0,1) =
    (Equiv.swap 0 2 * Equiv.swap 0 4,1) ∧
  RubikOBTM.Band.Finite.kernel (Equiv.swap 3 0,1) =
    (1,Equiv.swap 0 3 * Equiv.swap 0 13) ∧
  (Equiv.swap (0 : Fin 24) 2 * Equiv.swap 0 4).IsThreeCycle ∧
  (Equiv.swap (0 : Fin 24) 3 * Equiv.swap 0 13).IsThreeCycle := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · exact isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)
  · exact isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

private theorem RubikOBTM.Band.Finite.three_cycle_pairs_mem_range (σ : RubikOBTM.Band.Perm)
  (hσ : σ.IsThreeCycle) :
    (σ,1) ∈ RubikOBTM.Band.Finite.modelEval.range ∧
    (1,σ) ∈ RubikOBTM.Band.Finite.modelEval.range := by
  obtain ⟨hp, hm, hp3, hm3⟩ := RubikOBTM.Band.Finite.kernel_seeds
  constructor
  · obtain ⟨r, hr⟩ := _root_.isConj_iff.mp
      (Equiv.Perm.isConj_iff_cycleType_eq.mpr (hp3.cycleType.trans hσ.cycleType.symm))
    refine ⟨FreeGroup.of (r * Equiv.swap 2 0, r), ?_⟩
    change FreeGroup.lift kernel (FreeGroup.of (r * Equiv.swap 2 0, r)) = (σ,1)
    rw [FreeGroup.lift_apply_of]
    calc
      kernel (r * Equiv.swap 2 0, r) =
          (r,r) * kernel (Equiv.swap 2 0,1) * (r,r)⁻¹ := by
        simpa only [mul_one] using kernel_diagonal r (Equiv.swap 2 0) 1
      _ = (σ,1) := by rw [hp]; simp only [Prod.mk_mul_mk, Prod.inv_mk, mul_one, mul_inv_cancel, hr]
  · obtain ⟨r, hr⟩ := _root_.isConj_iff.mp
      (Equiv.Perm.isConj_iff_cycleType_eq.mpr (hm3.cycleType.trans hσ.cycleType.symm))
    refine ⟨FreeGroup.of (r * Equiv.swap 3 0, r), ?_⟩
    change FreeGroup.lift kernel (FreeGroup.of (r * Equiv.swap 3 0, r)) = (1,σ)
    rw [FreeGroup.lift_apply_of]
    calc
      kernel (r * Equiv.swap 3 0, r) =
          (r,r) * kernel (Equiv.swap 3 0,1) * (r,r)⁻¹ := by
        simpa only [mul_one] using kernel_diagonal r (Equiv.swap 3 0) 1
      _ = (1,σ) := by rw [hm]; simp only [Prod.mk_mul_mk, Prod.inv_mk, mul_one, mul_inv_cancel, hr]

private theorem RubikOBTM.Band.Finite.even_pair_range :
  (alternatingGroup RubikOBTM.Band.Label).prod (alternatingGroup RubikOBTM.Band.Label) ≤
    RubikOBTM.Band.Finite.modelEval.range := by
  have hplus : alternatingGroup Label ≤
      modelEval.range.comap (MonoidHom.inl Perm Perm) := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
    rw [Subgroup.closure_le]
    intro σ hσ
    exact (three_cycle_pairs_mem_range σ hσ).1
  have hminus : alternatingGroup Label ≤
      modelEval.range.comap (MonoidHom.inr Perm Perm) := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
    rw [Subgroup.closure_le]
    intro σ hσ
    exact (three_cycle_pairs_mem_range σ hσ).2
  rintro ⟨p,q⟩ ⟨hp,hq⟩
  simpa only [MonoidHom.inl_apply, MonoidHom.inr_apply, Prod.mk_mul_mk, one_mul, mul_one]
    using modelEval.range.mul_mem (hplus hp) (hminus hq)

private theorem RubikOBTM.Band.Finite.signedEval_eq_modelEval (w : List RubikOBTM.Band.Finite.Token) :
  RubikOBTM.Band.Finite.signedEval w =
    RubikOBTM.Band.Finite.modelEval (FreeGroup.mk w) := by
  simp only [signedEval, modelEval, FreeGroup.lift_mk]
  congr 1
  apply List.map_congr_left
  rintro ⟨a,b⟩ _
  cases b <;> rfl

theorem proof_RubikOBTM_Band_Finite_finite_signed_word_bound :
  ∃ M : ℕ, 0 < M ∧ ∀ p q : RubikOBTM.Band.Perm,
    p ∈ alternatingGroup RubikOBTM.Band.Label → q ∈ alternatingGroup RubikOBTM.Band.Label →
    ∃ w : List RubikOBTM.Band.Finite.Token,
      w.length ≤ M ∧ RubikOBTM.Band.Finite.signedEval w = (p,q) := by
  classical
  have hs : ∀ g : EvenPair, ∃ w : FreeGroup Alphabet,
      modelEval w = ((g.1 : Perm),(g.2 : Perm)) := by
    intro g
    exact even_pair_range ⟨g.1.property, g.2.property⟩
  choose f hf using hs
  let len (g : EvenPair) : ℕ := (f g).toWord.length
  let M : ℕ := Finset.univ.sup len + 1
  refine ⟨M, Nat.succ_pos _, ?_⟩
  intro p q hp hq
  let g : EvenPair := (⟨p,hp⟩,⟨q,hq⟩)
  refine ⟨(f g).toWord, ?_, ?_⟩
  · exact (Finset.le_sup (f := len) (Finset.mem_univ g)).trans (Nat.le_succ _)
  · rw [signedEval_eq_modelEval, FreeGroup.mk_toWord]
    exact hf g
