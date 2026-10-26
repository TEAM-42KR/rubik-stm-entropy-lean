import RubikSTM.Proofs.ExceptionalCentres.DiagonalUniformColoured
import RubikSTM.Definitions.ExceptionalCentres.WordPerm
set_option autoImplicit false

theorem RubikExceptional.DiagonalUniformColoured :
    ∃ C : ℕ, ∀ (n : ℕ) (a : Fin n), RubikExceptional.Regular n a →
    ∀ (c d : Rubik.Colouring n), Rubik.Reachable c → Rubik.Reachable d →
      ∃ w : List (Rubik.Move n), w.length ≤ C ∧
        (∀ i, Rubik.applyWord w c (RubikGeometry.lab a a i) = d (RubikGeometry.lab a a i)) ∧
        (∀ s, s ∉ Set.range (RubikGeometry.lab a a) → RubikExceptional.wordPerm w s = s) :=
  @proof_RubikExceptional_DiagonalUniformColoured
