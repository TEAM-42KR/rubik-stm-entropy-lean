import RubikSTM.Proofs.Orbits.MoveInvariant
import RubikSTM.Definitions.Orbits.RigidLabelPermutation
import RubikSTM.Definitions.Channel.Colour.Orbit
set_option autoImplicit false

theorem RubikOrbit.move_invariant :
    ∀ {n : ℕ} (a b : Fin n) (m : Rubik.Move n) (s : Rubik.Sticker n), Rubik.movePermutation m s ∈ Set.range (RubikGeometry.lab a b) ↔ s ∈ Set.range (RubikGeometry.lab a b) :=
  @proof_RubikOrbit_move_invariant
