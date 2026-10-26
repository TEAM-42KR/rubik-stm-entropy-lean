import RubikSTM.Proofs.OBTM.Band.WordPermApply
import RubikSTM.Definitions.OBTM.Band.CleanAction
set_option autoImplicit false

theorem RubikOBTM.Band.wordPerm_apply :
    ∀ {n : ℕ} (w : List (RubikOBTM.BlockMove n)) (c : Rubik.Colouring n) (s : Rubik.Sticker n), RubikOBTM.applyBlockWord w c s = c ((RubikOBTM.Band.wordPerm w)⁻¹ s) :=
  @proof_RubikOBTM_Band_wordPerm_apply
