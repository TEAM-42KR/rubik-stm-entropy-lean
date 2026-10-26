import RubikSTM.Definitions.FiniteProbability.ProductLaw
set_option autoImplicit false

namespace RubikAggregate

def overlapCount {L M : ℕ} (a b : Fin L → Fin M) : ℕ :=
  (Finset.univ.filter (fun i => b i = a i)).card

def overlapGraph (L M : ℕ) : SimpleGraph (Fin L → Fin M) where
  Adj a b := a ≠ b ∧ ∃ i, a i = b i
  symm := ⟨by
    intro a b hab
    refine ⟨Ne.symm hab.1, ?_⟩
    obtain ⟨i, hi⟩ := hab.2
    exact ⟨i, hi.symm⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

end RubikAggregate
