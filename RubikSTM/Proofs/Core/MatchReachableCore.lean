import RubikSTM.Definitions.Core.CoreAction
import RubikSTM.Lemmas.Core.ProjectWord
import RubikSTM.Lemmas.Core.CoreColouringCardLe
import RubikSTM.Lemmas.Core.FinitePermutationWordRollback
import RubikSTM.Lemmas.Core.FiniteWordCompression
set_option autoImplicit false

open Rubik RubikCore

theorem proof_RubikCore_match_reachable_core {n : ℕ} (c d : Position n) :
    ∃ w : List (Move n), w.length ≤ cleanupBound ∧
      project (applyWord w c.val) = project d.val := by
  classical
  obtain ⟨u, hu⟩ := c.property
  obtain ⟨v, hv⟩ := d.property
  have hucore : u.foldl (fun q m => coreAction m q) (project (solved n)) = project c.val := by
    rw [← RubikCore.project_word, hu]
  have hvcore : v.foldl (fun q m => coreAction m q) (project (solved n)) = project d.val := by
    rw [← RubikCore.project_word, hv]
  obtain ⟨r, hr⟩ := RubikCore.finite_permutation_word_rollback
    (fun m : Move n => coreAction m) u (project (solved n))
  rw [hucore] at hr
  have hconn : ∃ w : List (Move n),
      w.foldl (fun q m => coreAction m q) (project c.val) = project d.val := by
    refine ⟨r ++ v, ?_⟩
    rw [List.foldl_append, hr, hvcore]
  obtain ⟨w, hlen, hw⟩ := RubikCore.finite_word_compression
    (fun q m => coreAction m q) (project c.val) (project d.val) hconn
  refine ⟨w, hlen.le.trans (RubikCore.coreColouring_card_le n), ?_⟩
  rw [RubikCore.project_word]
  exact hw

#print axioms proof_RubikCore_match_reachable_core
