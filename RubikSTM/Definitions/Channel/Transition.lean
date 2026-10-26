import RubikSTM.Definitions.FiniteProbability.ProductLaw
import RubikSTM.Definitions.Codebook.LayerwiseUnion
set_option autoImplicit false

noncomputable section
open scoped BigOperators Classical

namespace RubikChannel

variable {C X : Type*} [Fintype C] [Fintype X]

def rowPermutation (σ : Equiv.Perm X) : Matrix X X ℝ :=
  fun x y => if σ x = y then 1 else 0

def transition (μ : RubikJanson.FiniteLaw C) (act : C → Equiv.Perm X) :
    Matrix X X ℝ :=
  fun x y => ∑ c, μ.weight c * rowPermutation (act c) x y

def wordLaw (μ : RubikJanson.FiniteLaw C) (L : ℕ) :
    RubikJanson.FiniteLaw (Fin L → C) :=
  { weight := fun w => ∏ i, μ.weight (w i)
    nonneg := fun w => Finset.prod_nonneg (fun i _ => μ.nonneg (w i))
    total := by
      rw [← Fintype.prod_sum]
      simp only [μ.total, Finset.prod_const_one] }

def run {L : ℕ} (act : Fin L → C → Equiv.Perm X)
    (w : Fin L → C) (x : X) : X :=
  (List.ofFn (fun i => act i (w i))).foldl (fun z σ => σ z) x

def wordMatrix (μ : RubikJanson.FiniteLaw C) {L : ℕ}
    (act : Fin L → C → Equiv.Perm X) : Matrix X X ℝ :=
  (List.ofFn (fun i => transition μ (act i))).prod

def freeze {L : ℕ} (fixed : Fin L → Option C) (w : Fin L → C) : Fin L → C :=
  fun i => (fixed i).getD (w i)

def mixedMatrix (μ : RubikJanson.FiniteLaw C) (act : C → Equiv.Perm X)
    {L : ℕ} (fixed : Fin L → Option C) : Matrix X X ℝ :=
  (List.ofFn (fun i => (fixed i).elim (transition μ act)
    (fun c => rowPermutation (act c)))).prod

def mixedPermutations (act : C → Equiv.Perm X) {L : ℕ}
    (fixed : Fin L → Option C) : List (Option (Equiv.Perm X)) :=
  List.ofFn (fun i => (fixed i).map act)

def Matches {L : ℕ} (fixed : Fin L → Option C) (w : Fin L → C) : Prop :=
  ∀ i c, fixed i = some c → w i = c

def fixedMass (μ : RubikJanson.FiniteLaw C) {L : ℕ}
    (fixed : Fin L → Option C) : ℝ :=
  ∏ i, (fixed i).elim 1 μ.weight

end RubikChannel
