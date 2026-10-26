import RubikSTM.Definitions.Bands.Band
import RubikSTM.Definitions.Wings.SolverWord
set_option autoImplicit false

theorem proof_RubikBand_wordBand {n : ℕ} (a : Fin n) (w : List (Rubik.Move n)) (s : Rubik.Sticker n) :
  RubikBand.Band a (RubikBand.wordPerm w s) ↔ RubikBand.Band a s := by
  induction w generalizing s with
  | nil => simp [RubikBand.wordPerm]
  | cons m w ih =>
    simp only [RubikBand.wordPerm, List.map_cons, List.reverse_cons,
      List.prod_append, List.prod_singleton, Equiv.Perm.mul_apply] at *
    exact (ih _).trans (RubikBand.moveBand a m s)

#print axioms proof_RubikBand_wordBand
