import RubikSTM.Definitions.GlobalWords.Region
import RubikSTM.Definitions.Core.CoreAction
import RubikSTM.Definitions.Grouping.GroupOf
set_option autoImplicit false

noncomputable section

namespace RubikCostBridge

def mNat (n : ℕ) : ℕ := (n - 2) / 2

def m (n : ℕ) : ℝ := mNat n

def hNat (n : ℕ) : ℕ := ⌈Real.log (m n) ^ 3⌉₊

def h (n : ℕ) : ℝ := hNat n

def block (ρ : ℝ) (s : ℕ) : ℕ :=
  ⌊(Real.log (s : ℝ) - 3 * Real.log (Real.log (s : ℝ))) / ρ⌋₊

instance colourOrbitFintype : Fintype (RubikChannel.Colour.Orbit RubikChannel.Paired.Seed) :=
  Fintype.ofFinite _

def q : ℝ := Fintype.card (RubikChannel.Colour.Orbit RubikChannel.Paired.Seed)

def d (n : ℕ) : ℝ := Rubik.diameter n

def CostEnvelope : Prop :=
  ∀ η : ℝ, 0 < η → ∃ L ρ C Cloc Cexc : ℝ,
    0 ≤ L ∧ 0 < ρ ∧ 0 ≤ C ∧ 0 ≤ Cloc ∧ 0 ≤ Cexc ∧
    L * ρ ≤ Real.log (q ^ 2) + η ∧
    ∀ᶠ n : ℕ in Filter.atTop, ∃ (G : ℕ) (r : Fin G → ℕ)
        (M : Fin G → Fin G → ℝ) (cnt : ℝ),
      (∀ i, ⌊m n / h n⌋₊ ≤ r i ∧ r i ≤ ⌊m n / h n⌋₊ + 1) ∧
      (∑ i, ∑ j, if i < j then ((r i : ℝ) * r j) else 0) ≤ m n ^ 2 / 2 ∧
      cnt ≤ m n ^ 2 / h n + m n ∧
      (∀ i j, M i j ≤ Real.exp (ρ * (block ρ (r j) : ℝ))) ∧
      d n ≤ (∑ i, ∑ j, if i < j then
          L * ((⌈(r i : ℝ) / (block ρ (r j) : ℝ)⌉₊ : ℝ) + 3)
            * ((r j : ℝ) + C * ((block ρ (r j) : ℝ) + 1) * M i j)
          else 0)
        + Cloc * cnt + Cexc * n

end RubikCostBridge
