import Mathlib
import RubikSTM.Definitions.Construction.Control.K
import RubikSTM.Lemmas.Construction.Control.StrictAOnlyTop
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open RubikConstruction.Control
theorem proof_RubikConstruction_Control_strict_deletion_realization (σ : Equiv.Perm (Fin 24)) :
    ∃ w : Word, finiteEval w = σ ∧ deletion w = 1 := by
  have hevalFace (k : Fin 6 → Fin 4) : finiteEval (freeFacePower k) = facePower k := by
    simp [freeFacePower, facePower, finiteEval, finiteAtom]
  have hsliceEval (i : Fin 3) : finiteEval (FreeGroup.of (Sum.inr i)) = slice i := by
    simp [finiteEval, finiteAtom]
  have hevalControl (t : ControlIndex) : finiteEval (freeControl t) = RubikConstruction.Control.control t := by
    simp only [freeControl, map_mul, map_inv, hevalFace, hsliceEval, RubikConstruction.Control.control]
  have hdeleteControl (t : ControlIndex) : deletion (freeControl t) = 1 := by
    simp [freeControl, deletion]
  have hg : ∀ g ∈ K, ∃ w : Word, finiteEval w = g ∧ deletion w = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨t, rfl⟩ := hg
      exact ⟨freeControl t, hevalControl t, hdeleteControl t⟩
    | one => exact ⟨1, map_one _, map_one _⟩
    | mul g h _ _ ihg ihh =>
      obtain ⟨u, hu, hdu⟩ := ihg
      obtain ⟨v, hv, hdv⟩ := ihh
      refine ⟨u * v, ?_, ?_⟩
      · rw [map_mul, hu, hv]
      · rw [map_mul, hdu, hdv, one_mul]
    | inv g _ ih =>
      obtain ⟨u, hu, hdu⟩ := ih
      refine ⟨u⁻¹, ?_, ?_⟩
      · rw [map_inv, hu]
      · rw [map_inv, hdu, inv_one]
  exact hg σ (by rw [strict_a_only_top]; trivial)
