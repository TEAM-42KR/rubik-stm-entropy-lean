import Mathlib
set_option autoImplicit false

namespace RubikJanson

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

def expect (P : FiniteLaw Ω) (f : Ω → ℝ) : ℝ := ∑ ω, P.weight ω * f ω

noncomputable def prob (P : FiniteLaw Ω) (event : Ω → Prop) : ℝ := by
  classical
  exact P.expect (fun ω => if event ω then 1 else 0)
end FiniteLaw

section
variable {ι Ω : Type*} [Fintype ι] [Fintype Ω]

def DependsOn (X : ι → Ω → ℝ) (A : Finset ι) (f : Ω → ℝ) : Prop :=
  ∀ ω ω', (∀ i ∈ A, X i ω = X i ω') → f ω = f ω'

def StrongDependency (P : FiniteLaw Ω) (X : ι → Ω → ℝ)
    (G : SimpleGraph ι) : Prop :=
  ∀ A B : Finset ι, Disjoint A B →
    (∀ i ∈ A, ∀ j ∈ B, ¬ G.Adj i j) →
    ∀ f g : Ω → ℝ, DependsOn X A f → DependsOn X B g →
      P.expect (fun ω => f ω * g ω) = P.expect f * P.expect g

def IsBernoulli (X : ι → Ω → ℝ) : Prop :=
  ∀ i ω, X i ω = 0 ∨ X i ω = 1

def IsBounded (X : ι → Ω → ℝ) : Prop :=
  ∀ i ω, 0 ≤ X i ω ∧ X i ω ≤ 1

def mean (P : FiniteLaw Ω) (X : ι → Ω → ℝ) (i : ι) : ℝ := P.expect (X i)

def nu (P : FiniteLaw Ω) (X : ι → Ω → ℝ) : ℝ := ∑ i, mean P X i

noncomputable def neighbors (G : SimpleGraph ι) (i : ι) : Finset ι := by
  classical
  exact Finset.univ.filter (G.Adj i)

noncomputable def pairNeighbors (G : SimpleGraph ι) (i j : ι) : Finset ι := by
  classical
  exact neighbors G i ∪ neighbors G j

noncomputable def neighborMean (P : FiniteLaw Ω) (X : ι → Ω → ℝ)
    (G : SimpleGraph ι) (i : ι) : ℝ := ∑ j ∈ neighbors G i, mean P X j

noncomputable def delta (P : FiniteLaw Ω) (X : ι → Ω → ℝ)
    (G : SimpleGraph ι) : ℝ := by
  classical
  exact (insert 0 (Finset.univ.image (neighborMean P X G))).sup' (by simp) id

noncomputable def Delta (P : FiniteLaw Ω) (X : ι → Ω → ℝ)
    (G : SimpleGraph ι) : ℝ :=
  (∑ i, ∑ j ∈ neighbors G i, P.expect (fun ω => X i ω * X j ω)) / 2

noncomputable def zeroProb (P : FiniteLaw Ω) (X : ι → Ω → ℝ) : ℝ :=
  P.prob (fun ω => ∀ i, X i ω = 0)

noncomputable def interp (P : FiniteLaw Ω) (X : ι → Ω → ℝ)
    (A : Finset ι) (t : ℝ) (ω : Ω) : ℝ :=
  ∏ i ∈ A, (1 - mean P X i - t * (X i ω - mean P X i))

noncomputable def deficitProduct (P : FiniteLaw Ω) (X : ι → Ω → ℝ)
    (A : Finset ι) : ℝ := ∏ i ∈ A, (1 - mean P X i)

noncomputable def edgeCost (P : FiniteLaw Ω) (X : ι → Ω → ℝ)
    (G : SimpleGraph ι) (i j : ι) : ℝ :=
  P.expect (fun ω => X i ω * X j ω) /
    deficitProduct P X (pairNeighbors G i j)

noncomputable def suenCost (P : FiniteLaw Ω) (X : ι → Ω → ℝ)
    (G : SimpleGraph ι) : ℝ :=
  (∑ i, ∑ j ∈ neighbors G i, edgeCost P X G i j) / 2

end
end RubikJanson
