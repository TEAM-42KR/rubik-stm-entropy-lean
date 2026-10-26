import RubikSTM.Proofs.OBTM.Global.RecolourFromStm
import RubikSTM.Definitions.OBTM.Global.RectangleCompiler
set_option autoImplicit false

theorem RubikOBTM.Global.recolour_from_stm :
    ∀ {n : ℕ} (hn : 2 ≤ n) (S : Set (Rubik.Sticker n)) (c d : Rubik.Colouring n) (w : List (Rubik.Move n)) (hw : RubikGlobalWord.Recolour S c d w), ∃ v : List (RubikOBTM.BlockMove n), v.length ≤ 2 * w.length ∧ RubikOBTM.Global.Recolour S c d v :=
  @proof_RubikOBTM_Global_recolour_from_stm
