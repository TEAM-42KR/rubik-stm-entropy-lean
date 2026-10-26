import RubikSTM.Proofs.Channel.Paired.UniversalCodebook
import RubikSTM.Definitions.Channel.Paired.P
import RubikSTM.Definitions.UniversalCodebooks.PathIndicator
set_option autoImplicit false

theorem RubikChannel.Paired.universalCodebook :
    ∀ (η : ℝ) (hη : 0 < η), ∃ L : ℕ, 0 < L ∧ 4 ∣ L ∧ ∃ r : ℝ, 0 < r ∧ (L : ℝ) * r < Real.log (Fintype.card RubikChannel.Paired.State) + η ∧ ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∃ B : RubikCodebook.Book RubikChannel.Paired.Letter k L, RubikCodebook.CoversAll RubikChannel.Paired.act B ∧ ∀ i : Fin L, ((B i).card : ℝ) ≤ Real.exp ((k : ℝ) * r) :=
  @proof_RubikChannel_Paired_universalCodebook
