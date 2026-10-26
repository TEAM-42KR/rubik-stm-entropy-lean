import RubikSTM.Definitions.Core.CoreAction
import RubikSTM.Lemmas.Core.MatchCorePointwise
set_option autoImplicit false

open Rubik RubikCore

theorem proof_RubikCore_cleanup_to_solved {n : ℕ} (c : Position n) :
    ∃ w : List (Move n), w.length ≤ cleanupBound ∧
      ∀ s : Sticker n, IsCore s → applyWord w c.val s = solved n s := by
  let d : Position n := ⟨solved n, ⟨[], rfl⟩⟩
  exact RubikCore.match_core_pointwise c d

#print axioms proof_RubikCore_cleanup_to_solved
