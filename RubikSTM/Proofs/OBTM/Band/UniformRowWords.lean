import RubikSTM.Definitions.OBTM.Band.CleanAction
import RubikSTM.Lemmas.OBTM.Band.PhysicalControlStrict
import RubikSTM.Lemmas.OBTM.Band.RowActionBoth
import RubikSTM.Lemmas.Construction.Control.Physical.UniformSignedModel
import RubikSTM.Lemmas.Construction.Control.Physical.ActualMovesEval
import RubikSTM.Lemmas.Construction.Control.Physical.ActualMovesDeletion
import RubikSTM.Lemmas.Construction.Control.Physical.ActualMovesAllowed
import RubikSTM.Lemmas.Construction.Control.Physical.ChronologicalAlgebra
set_option autoImplicit false
open Rubik RubikConstruction.Control RubikConstruction.Control.Physical RubikOBTM.Band

theorem proof_RubikOBTM_Band_uniform_row_words : ∃ L : ℕ, ∀ (n : ℕ) (a : Fin n),
    1 ≤ a.val → 2*a.val+2 ≤ n → ∀ σ : Equiv.Perm (Fin 24),
    ∃ ms : List (Move n), ms.length ≤ L ∧ RubikBand.StrictControl a ms ∧
      ∀ (d : Fin n), 1 ≤ d.val → 2*d.val+2 ≤ n → a ≠ d → ∀ i : Fin 24,
        (RubikBand.wordPerm ms (plus a d i) = plus a d (σ i)) ∧
        (RubikBand.wordPerm ms (minus a d i) = minus a d (σ i)) := by
  obtain ⟨L,hL⟩ := uniform_signed_model
  refine ⟨L,?_⟩
  intro n a ha has σ
  obtain ⟨letters,hlen,hfin,hdel⟩ := hL σ
  let ms := actualMoves a letters
  have he : RubikBand.wordPerm ms = physicalEval a (FreeGroup.mk letters) := by
    calc
      RubikBand.wordPerm ms = chronological ms := by
        simpa [RubikBand.wordPerm,List.map_reverse] using (chronological_algebra ms).symm
      _ = physicalEval a (FreeGroup.mk letters) := actual_moves_eval a letters
  refine ⟨ms,?_,?_,?_⟩
  · simpa [ms,actualMoves] using hlen
  · apply physical_control_strict a ha has ms (actual_moves_allowed a letters)
    rw [actual_moves_deletion a ha has]
    change physicalFaceEval a (deletion (FreeGroup.mk letters)) = 1
    rw [hdel,map_one]
  · intro d hd hds had i
    rw [he]
    simpa [hfin] using row_action_both a d ha hd has hds had (FreeGroup.mk letters) i
