import RubikSTM.Proofs.OBTM.ObtmGraphWalkWord
import RubikSTM.Definitions.OBTM.ObtmGraph
set_option autoImplicit false

theorem RubikOBTM.obtmGraph_walk_word :
    ∀ {n : ℕ} {u v : Rubik.Position n} (p : (RubikOBTM.obtmGraph n).Walk u v), ∃ w : List (RubikOBTM.BlockMove n), w.length = p.length ∧ RubikOBTM.applyBlockWord w u.val = v.val :=
  @proof_RubikOBTM_obtmGraph_walk_word
