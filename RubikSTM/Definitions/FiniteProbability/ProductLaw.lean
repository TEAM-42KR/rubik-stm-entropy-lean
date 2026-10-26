import RubikSTM.Definitions.FiniteProbability.FiniteLaw
set_option autoImplicit false

namespace RubikJanson
open scoped Classical

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]

def NonedgeIndependent (P : FiniteLaw Ω) (X : ι → Ω → ℝ)
    (G : SimpleGraph ι) : Prop :=
  ∀ i j, i ≠ j → ¬ G.Adj i j →
    P.expect (fun ω => X i ω * X j ω) = mean P X i * mean P X j

noncomputable def productLaw {κ : Type*} [Fintype κ]
    (P : κ → FiniteLaw Ω) : FiniteLaw (κ → Ω) := by
  classical
  exact
    { weight := fun ω => ∏ i, (P i).weight (ω i)
      nonneg := fun ω => Finset.prod_nonneg (fun i _ => (P i).nonneg (ω i))
      total := by
        rw [← Fintype.prod_sum]
        simp only [FiniteLaw.total, Finset.prod_const_one] }

noncomputable def uniformLaw (hΩ : Nonempty Ω) : FiniteLaw Ω := by
  classical
  letI := hΩ
  exact
    { weight := fun _ => 1 / (Fintype.card Ω : ℝ)
      nonneg := fun _ => by positivity
      total := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        exact mul_one_div_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) }

noncomputable def layerUnion {κ Layer Word : Type*} [Fintype κ]
    (D : κ → Layer → Finset Word) (i : Layer) : Finset Word := by
  classical
  exact Finset.univ.biUnion (fun u => D u i)

def HasPath {Layer Word Endpoint : Type*} (D : Layer → Finset Word)
    (Path : Endpoint → (Layer → Word) → Prop) (e : Endpoint) : Prop :=
  ∃ w : Layer → Word, (∀ i, w i ∈ D i) ∧ Path e w

end RubikJanson
