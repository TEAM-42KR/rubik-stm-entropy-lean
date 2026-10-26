import RubikSTM.Definitions.OBTM.Global.RectangleCompiler
import RubikSTM.Lemmas.OBTM.SliceWordToBlocks
set_option autoImplicit false

theorem proof_RubikOBTM_Global_recolour_from_stm {n : ℕ} (hn : 2 ≤ n) (S : Set (Rubik.Sticker n))
    (c d : Rubik.Colouring n) (w : List (Rubik.Move n))
    (hw : RubikGlobalWord.Recolour S c d w) :
    ∃ v : List (RubikOBTM.BlockMove n),
      v.length ≤ 2 * w.length ∧ RubikOBTM.Global.Recolour S c d v := by
  obtain ⟨v,hv,hact⟩ := RubikOBTM.sliceWord_to_blocks hn w
  exact ⟨v,hv,by simpa only [RubikOBTM.Global.Recolour,RubikGlobalWord.Recolour,hact] using hw⟩
