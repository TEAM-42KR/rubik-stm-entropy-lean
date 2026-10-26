import RubikSTM.Definitions.Rectangles.PayloadInterface
import RubikSTM.Lemmas.Bands.SameAxisFourth
set_option autoImplicit false

theorem proof_RubikRectangle_columnBaseline_four {n : ℕ} (Y : Finset (Fin n)) : RubikPayload.columnBaseline Y ^ 4 = 1 := by
  simpa [RubikPayload.columnBaseline, RubikPayload.baselineWord, RubikBand.wordPerm,
    List.map_map, Function.comp_def, Rubik.movePermutation] using
    RubikBand.sameAxisFourth (n := n) 2 ((Y.sort (· ≤ ·)).map Fin.rev)

#print axioms proof_RubikRectangle_columnBaseline_four
