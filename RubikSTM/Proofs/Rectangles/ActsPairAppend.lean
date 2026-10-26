import RubikSTM.Definitions.Rectangles.PayloadInterface
set_option autoImplicit false

open RubikRectangle RubikPayload

theorem proof_RubikRectangle_actsPair_append {n : ℕ} (a b : Fin n) (hb : 0 < b.val ∧ b.val + 1 < n)
    (u v : List (Rubik.Move n)) (g h : Pair)
    (hu : ActsPair a b hb u g) (hv : ActsPair a b hb v h) :
    ActsPair a b hb (u ++ v) (h * g) := by
  have he : RubikBand.wordPerm (u ++ v) = RubikBand.wordPerm v * RubikBand.wordPerm u := by
    simp [RubikBand.wordPerm, List.map_append, List.reverse_append, List.prod_append]
  constructor
  · intro i
    rw [he, Equiv.Perm.mul_apply, hu.1, hv.1]
    rfl
  · intro i
    rw [he, Equiv.Perm.mul_apply, hu.2, hv.2]
    rfl

#print axioms proof_RubikRectangle_actsPair_append
