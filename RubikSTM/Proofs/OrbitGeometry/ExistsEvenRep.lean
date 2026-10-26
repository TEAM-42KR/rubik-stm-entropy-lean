import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open Rubik RubikGeometry
theorem proof_RubikGeometry_exists_even_rep (σ : Equiv.Perm (Fin 24)) :
    ∃ σ' ∈ alternatingGroup (Fin 24), normalTable ∘ σ' = normalTable ∘ σ := by
  by_cases hσ : σ ∈ alternatingGroup (Fin 24)
  · exact ⟨σ, hσ, rfl⟩
  have hs : Equiv.Perm.sign σ = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · exact False.elim (hσ (Equiv.Perm.mem_alternatingGroup.mpr h))
    · exact h
  refine ⟨Equiv.swap (0 : Fin 24) 1 * σ, ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap (by decide), hs]
    decide
  · have ht : normalTable ∘ Equiv.swap (0 : Fin 24) 1 = normalTable := by decide
    change (normalTable ∘ Equiv.swap (0 : Fin 24) 1) ∘ σ = normalTable ∘ σ
    rw [ht]
