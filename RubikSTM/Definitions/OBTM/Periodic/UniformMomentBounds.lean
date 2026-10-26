import RubikSTM.Definitions.OBTM.Periodic.SampleLaw
set_option autoImplicit false
noncomputable section

namespace RubikOBTM.Periodic

def lowerEnvelope (q θ : ℝ) (L T : ℕ) : ℝ := 1 / q - θ ^ (L / T)

def ratioEnvelope (q m ρ : ℝ) (s : ℕ) : ℝ :=
  min (1 / m) ((1 / q ^ 2 + ρ ^ s) / m ^ 2)

def MomentEstimates {T : ℕ} {Z : Type*} (hT : 0 < T) (K : Fin T → Type*)
    [∀ p, Group (K p)] (C : ∀ p, Finset (K p)) (hC : ∀ p, (C p).Nonempty)
    (act : ∀ p, K p →* Equiv.Perm Z) (L : ℕ) (m : ℝ) (R : ℕ → ℝ) : Prop :=
  ∀ k M : ℕ, ∀ x y : Fin k → Z, ∀ n : Profile hT K k L,
    ∃ π : ℝ, m ^ k ≤ π ∧
      (∀ a, RubikJanson.mean (sampleLaw hT K C hC k L M)
        (pathIndicator hT K C act x y n) a = π) ∧
      (∀ a b, (RubikAggregate.overlapGraph L M).Adj a b →
        (sampleLaw hT K C hC k L M).expect
          (fun W => pathIndicator hT K C act x y n a W *
            pathIndicator hT K C act x y n b W) ≤
              π ^ 2 * R (L - RubikAggregate.overlapCount a b) ^ k)

def UniformMomentBounds {T : ℕ} {Z : Type*} [Fintype Z] (hT : 0 < T)
    (K : Fin T → Type*) [∀ p, Group (K p)] (C : ∀ p, Finset (K p))
    (hC : ∀ p, (C p).Nonempty) (act : ∀ p, K p →* Equiv.Perm Z) (θ ρ : ℝ) : Prop :=
  ∀ L : ℕ, 0 < L → T ∣ L → 0 < lowerEnvelope (Fintype.card Z) θ L T →
    MomentEstimates hT K C hC act L (lowerEnvelope (Fintype.card Z) θ L T)
      (ratioEnvelope (Fintype.card Z) (lowerEnvelope (Fintype.card Z) θ L T) ρ)

end RubikOBTM.Periodic
