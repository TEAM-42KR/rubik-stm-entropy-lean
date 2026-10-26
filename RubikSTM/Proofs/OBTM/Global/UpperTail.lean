import RubikSTM.Definitions.OBTM.ObtmGraph
import RubikSTM.Lemmas.OBTM.Global.ActualWordCostEnvelope
import RubikSTM.Lemmas.OBTM.Global.UpperTailOfWordEnvelope
set_option autoImplicit false

theorem proof_RubikOBTM_Global_upperTail (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop,
      RubikOBTM.normalizedDiameter n ≤ Rubik.entropyConstant + ε :=
  RubikOBTM.Global.upperTail_of_wordEnvelope RubikOBTM.Global.actual_word_cost_envelope ε hε
