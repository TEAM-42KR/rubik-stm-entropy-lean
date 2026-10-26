import RubikSTM.Definitions.Bands.Band
import RubikSTM.Definitions.Wings.SolverWord
set_option autoImplicit false

theorem proof_RubikBand_baselineBand {n : ℕ} (a : Fin n) (q : Rubik.Axis) (Y : Finset (Fin n))
  (s : Rubik.Sticker n) :
  RubikBand.Band a (RubikBand.parallelBaseline q Y s) ↔ RubikBand.Band a s := by
  have hp : ∀ ls : List (Fin n), ∀ t : Rubik.Sticker n,
      RubikBand.Band a (((ls.map (Rubik.sliceQuarter n q)).reverse.prod) t) ↔ RubikBand.Band a t := by
    intro ls
    induction ls with
    | nil => intro t; rfl
    | cons l ls ih =>
      intro t
      simp only [List.map_cons, List.reverse_cons, List.prod_append,
        List.prod_singleton, Equiv.Perm.mul_apply]
      exact (ih _).trans (RubikBand.sliceBand a l q t)
  exact hp _ s

#print axioms proof_RubikBand_baselineBand
