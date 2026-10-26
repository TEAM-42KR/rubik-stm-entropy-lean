import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Lemmas.WordConstruction.WordColouring
set_option autoImplicit false

theorem proof_RubikOBTM_blockWord_action {n : ℕ} (w : List (RubikOBTM.BlockMove n)) (c : Rubik.Colouring n) :
    RubikOBTM.applyBlockWord w c = fun s => c (((w.map RubikOBTM.blockPermutation).reverse.prod)⁻¹ s) := by
  exact RubikCompiler.wordColouring RubikOBTM.blockPermutation w c
