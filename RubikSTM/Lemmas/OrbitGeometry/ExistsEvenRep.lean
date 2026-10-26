import RubikSTM.Proofs.OrbitGeometry.ExistsEvenRep
import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
set_option autoImplicit false
open Rubik

theorem RubikGeometry.exists_even_rep :
    ∀ (σ : Equiv.Perm (Fin 24)), ∃ σ' ∈ alternatingGroup (Fin 24), normalTable ∘ σ' = normalTable ∘ σ :=
  @proof_RubikGeometry_exists_even_rep
