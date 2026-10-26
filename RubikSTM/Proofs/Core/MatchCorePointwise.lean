import RubikSTM.Definitions.Core.CoreAction
import RubikSTM.Lemmas.Core.MatchReachableCore
set_option autoImplicit false

open Rubik RubikCore

theorem proof_RubikCore_match_core_pointwise {n : ℕ} (c d : Position n) :
    ∃ w : List (Move n), w.length ≤ cleanupBound ∧
      ∀ s : Sticker n, IsCore s → applyWord w c.val s = d.val s := by
  obtain ⟨w, hlen, hw⟩ := RubikCore.match_reachable_core c d
  refine ⟨w, hlen, ?_⟩
  intro s hs
  exact congrFun hw (⟨s, hs⟩ : CoreSticker n)

#print axioms proof_RubikCore_match_core_pointwise
