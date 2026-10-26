import RubikSTM.Definitions.Channel.Transition
set_option autoImplicit false

noncomputable section
open scoped BigOperators Classical
namespace RubikChannel

def arrayLaw {C : Type*} [Fintype C] (μ : RubikJanson.FiniteLaw C)
    (k L : ℕ) : RubikJanson.FiniteLaw (Fin L → Fin k → C) where
  weight w := ∏ i, ∏ j, μ.weight (w i j)
  nonneg w := Finset.prod_nonneg (fun i _ =>
    Finset.prod_nonneg (fun j _ => μ.nonneg (w i j)))
  total := by
    have hrow : (∑ row : Fin k → C, ∏ j, μ.weight (row j)) = 1 :=
      (wordLaw μ k).total
    calc
      (∑ w : Fin L → Fin k → C, ∏ i, ∏ j, μ.weight (w i j)) =
          ∏ _i : Fin L, ∑ row : Fin k → C, ∏ j, μ.weight (row j) :=
        (Fintype.prod_sum (fun (_i : Fin L) (row : Fin k → C) =>
          ∏ j, μ.weight (row j))).symm
      _ = 1 := by simp only [hrow, Finset.prod_const_one]

def freezeArray {C : Type*} {k L : ℕ} (fixed : Fin L → Fin k → Option C)
    (w : Fin L → Fin k → C) : Fin L → Fin k → C :=
  fun i j => (fixed i j).getD (w i j)

def MatchesArray {C : Type*} {k L : ℕ}
    (fixed : Fin L → Fin k → Option C) (w : Fin L → Fin k → C) : Prop :=
  ∀ i j c, fixed i j = some c → w i j = c

end RubikChannel
