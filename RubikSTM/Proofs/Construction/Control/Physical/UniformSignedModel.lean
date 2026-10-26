import Mathlib
import RubikSTM.Definitions.Construction.Control.Physical.ActualMoves
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Lemmas.Construction.Control.StrictDeletionRealization
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open Rubik RubikConstruction.Control RubikConstruction.Control.Physical
theorem proof_RubikConstruction_Control_Physical_uniform_signed_model :
    ∃ L : ℕ, ∀ σ : Equiv.Perm (Fin 24), ∃ letters : List SignedLetter,
      letters.length ≤ L ∧ finiteEval (FreeGroup.mk letters) = σ ∧ deletion (FreeGroup.mk letters) = 1 := by
  classical
  have hmodel (σ : Equiv.Perm (Fin 24)) :
      ∃ letters : List SignedLetter, finiteEval (FreeGroup.mk letters) = σ ∧ deletion (FreeGroup.mk letters) = 1 := by
    obtain ⟨w, hw, hd⟩ := strict_deletion_realization σ
    obtain ⟨letters, he⟩ : ∃ letters : List SignedLetter, FreeGroup.mk letters = w :=
      Quot.inductionOn w (fun letters => ⟨letters, rfl⟩)
    exact ⟨letters, he ▸ hw, he ▸ hd⟩
  choose words hword using hmodel
  refine ⟨Finset.univ.sup (fun σ => (words σ).length), ?_⟩
  intro σ
  exact ⟨words σ, Finset.le_sup (f := fun σ : Equiv.Perm (Fin 24) => (words σ).length) (Finset.mem_univ σ), (hword σ).1, (hword σ).2⟩
