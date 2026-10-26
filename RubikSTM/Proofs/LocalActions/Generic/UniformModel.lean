import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Definitions.LocalActions.Generic.ModelEval
import RubikSTM.Lemmas.LocalActions.Generic.ModelEvalMk
import RubikSTM.Lemmas.LocalActions.Generic.AlternatingRange
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
open Rubik RubikGeometry
open RubikLocal.Generic RubikConstruction.Control.Physical
theorem proof_RubikLocal_Generic_uniform_model : ∃ M : ℕ, ∀ τ : Equiv.Perm (Fin 24),
    τ ∈ alternatingGroup (Fin 24) → ∃ ts : List Token, ts.length ≤ M ∧ evalTokens ts = τ := by
  classical
  letI : Fintype (alternatingGroup (Fin 24)) := Fintype.ofFinite _
  have hrep (τ : alternatingGroup (Fin 24)) : ∃ ts : List Token, evalTokens ts = τ.val := by
    obtain ⟨w, hw⟩ := alternating_range τ.property
    obtain ⟨ts, he⟩ : ∃ ts : List Token, FreeGroup.mk ts = w :=
      Quot.inductionOn w (fun ts => ⟨ts, rfl⟩)
    exact ⟨ts, (model_eval_mk ts).symm.trans (he ▸ hw)⟩
  choose words hw using hrep
  refine ⟨Finset.univ.sup (fun τ => (words τ).length), ?_⟩
  intro τ hτ
  let t : alternatingGroup (Fin 24) := ⟨τ, hτ⟩
  exact ⟨words t, Finset.le_sup (f := fun τ => (words τ).length) (Finset.mem_univ t), hw t⟩
