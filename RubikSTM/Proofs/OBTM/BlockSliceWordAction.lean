import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Lemmas.OBTM.BlockSliceWordPermutation
import RubikSTM.Lemmas.WordConstruction.WordColouring
set_option autoImplicit false

theorem proof_RubikOBTM_blockSliceWord_action {n : ℕ} (m : RubikOBTM.BlockMove n) (c : Rubik.Colouring n) :
    Rubik.applyWord (RubikOBTM.blockSliceWord m) c = RubikOBTM.applyBlock m c := by
  change (RubikOBTM.blockSliceWord m).foldl
    (fun state m => fun s => state ((Rubik.movePermutation m)⁻¹ s)) c = _
  rw [RubikCompiler.wordColouring, RubikOBTM.blockSliceWord_permutation]
  rfl
