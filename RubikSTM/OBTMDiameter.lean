import RubikSTM.Lemmas.OBTM.OBTMSharpDiameter

theorem RubikSTM.rubik_obtm_diameter_entropy : Filter.Tendsto RubikOBTM.normalizedDiameter Filter.atTop (nhds Rubik.entropyConstant) := @RubikOBTM.OBTMSharpDiameter
