import RubikSTM.Proofs.ExceptionalCentres.CrossUniformColoured
import RubikSTM.Definitions.ExceptionalCentres.CrossThreeCycle
set_option autoImplicit false

theorem RubikExceptional.CrossUniformColoured :
    ∃ C : ℕ, ∀ (n : ℕ) (a b : Fin n), RubikExceptional.Regular n a → b.rev = b →
    ∀ (c d : Rubik.Colouring n), Rubik.Reachable c → Rubik.Reachable d →
      ∃ w : List (Rubik.Move n), w.length ≤ C ∧
        (∀ i, Rubik.applyWord w c (RubikGeometry.lab a b i) = d (RubikGeometry.lab a b i)) ∧
        (∀ s, s ∉ Set.range (RubikGeometry.lab a b) → RubikExceptional.wordPerm w s = s) :=
  @proof_RubikExceptional_CrossUniformColoured
