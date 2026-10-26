import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Lemmas.OBTM.Global.LowerTail
import RubikSTM.Lemmas.OBTM.Global.UpperTail
set_option autoImplicit false
open Filter Topology

theorem proof_RubikOBTM_OBTMSharpDiameter :
    Filter.Tendsto RubikOBTM.normalizedDiameter Filter.atTop (nhds Rubik.entropyConstant) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    have hε : 0 < (Rubik.entropyConstant - a) / 2 := by linarith
    filter_upwards [RubikOBTM.Global.lowerTail ((Rubik.entropyConstant - a) / 2) hε] with n hn
    linarith
  · intro b hb
    have hε : 0 < (b - Rubik.entropyConstant) / 2 := by linarith
    filter_upwards [RubikOBTM.Global.upperTail ((b - Rubik.entropyConstant) / 2) hε] with n hn
    linarith
