import RubikSTM.Definitions.ExceptionalCentres.DiagQuarterMove
set_option autoImplicit false

def RubikExceptional.wordPerm {n : ℕ} (w : List (Rubik.Move n)) :
    Equiv.Perm (Rubik.Sticker n) := (w.map Rubik.movePermutation).reverse.prod

def RubikExceptional.inverseMove {n : ℕ} (m : Rubik.Move n) : Rubik.Move n :=
  (m.1,m.2.1,m.2.2.rev)

def RubikExceptional.inverseWord {n : ℕ} (w : List (Rubik.Move n)) : List (Rubik.Move n) :=
  w.reverse.map RubikExceptional.inverseMove

def RubikExceptional.DiagonalSolves {n : ℕ} (a : Fin n)
    (τ : Equiv.Perm (Fin 24)) (w : List (Rubik.Move n)) : Prop :=
  (∀ i, RubikExceptional.wordPerm w (RubikGeometry.lab a a i) = RubikGeometry.lab a a (τ i)) ∧
  ∀ s, s ∉ Set.range (RubikGeometry.lab a a) → RubikExceptional.wordPerm w s = s
