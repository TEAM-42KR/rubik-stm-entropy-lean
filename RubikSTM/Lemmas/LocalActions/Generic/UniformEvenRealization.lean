import RubikSTM.Proofs.LocalActions.Generic.UniformEvenRealization
import RubikSTM.Definitions.LocalActions.Generic.ModelEval
set_option autoImplicit false
open RubikLocal.Generic RubikConstruction.Control.Physical

theorem RubikLocal.Generic.uniform_even_realization :
    ∃ C : ℕ, ∀ (n : ℕ) (a b : Fin n), RubikGeometry.Generic n a b → ∀ τ : Equiv.Perm (Fin 24), τ ∈ alternatingGroup (Fin 24) → ∃ ms : List (Rubik.Move n), ms.length ≤ C ∧ RubikLocal.Generic.LocalAction a b τ (RubikConstruction.Control.Physical.chronological ms) :=
  @proof_RubikLocal_Generic_uniform_even_realization
