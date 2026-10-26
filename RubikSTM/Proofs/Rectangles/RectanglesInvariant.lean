import RubikSTM.Definitions.Rectangles.PayloadInterface
import RubikSTM.Lemmas.Orbits.MoveInvariant
set_option autoImplicit false

theorem proof_RubikRectangle_rectangles_invariant {n : ℕ} (X Y : Finset (Fin n)) (w : List (Rubik.Move n))
    (s : Rubik.Sticker n) :
    RubikPayload.Rectangles X Y (RubikBand.wordPerm w s) ↔
      RubikPayload.Rectangles X Y s := by
  have hword (a b : Fin n) (w : List (Rubik.Move n)) (s : Rubik.Sticker n) :
      RubikBand.wordPerm w s ∈ Set.range (RubikGeometry.lab a b) ↔
        s ∈ Set.range (RubikGeometry.lab a b) := by
    induction w generalizing s with
    | nil => rfl
    | cons m w ih =>
      have he : RubikBand.wordPerm (m :: w) = RubikBand.wordPerm w * Rubik.movePermutation m := by
        simp [RubikBand.wordPerm]
      rw [he, Equiv.Perm.mul_apply, ih, RubikOrbit.move_invariant]
  unfold RubikPayload.Rectangles
  simp only [Set.mem_union, hword]

#print axioms proof_RubikRectangle_rectangles_invariant
