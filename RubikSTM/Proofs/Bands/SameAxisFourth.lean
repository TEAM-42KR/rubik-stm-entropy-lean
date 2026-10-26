import RubikSTM.Definitions.Bands.Band
import RubikSTM.Lemmas.Bands.SliceCommute
import RubikSTM.Definitions.Wings.SolverWord
set_option autoImplicit false

theorem proof_RubikBand_sameAxisFourth {n : ℕ} (q : Rubik.Axis) (ls : List (Fin n)) :
  ((ls.map (Rubik.sliceQuarter n q)).reverse.prod) ^ 4 = 1 := by
  have comm : ∀ k : Fin n, ∀ ls : List (Fin n),
      Commute (Rubik.sliceQuarter n q k) ((ls.map (Rubik.sliceQuarter n q)).reverse.prod) := by
    intro k ls
    induction ls with
    | nil => simp
    | cons l ls ih =>
      simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton]
      exact ih.mul_right (RubikBand.sliceCommute q k l)
  induction ls with
  | nil => simp
  | cons l ls ih =>
    simp only [List.map_cons, List.reverse_cons, List.prod_append, List.prod_singleton]
    rw [(comm l ls).symm.mul_pow, ih, Rubik.sliceQuarter_order_four, one_mul]

#print axioms proof_RubikBand_sameAxisFourth
