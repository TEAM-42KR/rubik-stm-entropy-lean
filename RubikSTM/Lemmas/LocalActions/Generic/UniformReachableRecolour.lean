import RubikSTM.Proofs.LocalActions.Generic.UniformReachableRecolour
import RubikSTM.Definitions.LocalActions.Generic.ModelEval
set_option autoImplicit false
open RubikLocal.Generic RubikConstruction.Control.Physical

theorem RubikLocal.Generic.uniform_reachable_recolour :
    ∃ C : ℕ, ∀ (n : ℕ) (a b : Fin n), RubikGeometry.Generic n a b → ∀ c d : Rubik.Colouring n, Rubik.Reachable c → Rubik.Reachable d → ∃ ms : List (Rubik.Move n), ms.length ≤ C ∧ (∀ i : Fin 24, Rubik.applyWord ms c (RubikGeometry.lab a b i) = d (RubikGeometry.lab a b i)) ∧ (∀ s : Rubik.Sticker n, s ∉ Set.range (RubikGeometry.lab a b) → RubikConstruction.Control.Physical.chronological ms s = s) ∧ (∀ s : Rubik.Sticker n, s ∉ Set.range (RubikGeometry.lab a b) → Rubik.applyWord ms c s = c s) :=
  @proof_RubikLocal_Generic_uniform_reachable_recolour
