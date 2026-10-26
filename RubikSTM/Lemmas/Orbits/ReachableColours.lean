import RubikSTM.Proofs.Orbits.ReachableColours
import RubikSTM.Definitions.Orbits.RigidLabelPermutation
import RubikSTM.Definitions.Channel.Colour.Orbit
set_option autoImplicit false

theorem RubikOrbit.reachable_colours :
    ∀ {n : ℕ} {a b : Fin n} (hg : RubikGeometry.Generic n a b) (c : Rubik.Colouring n) (hc : Rubik.Reachable c), ∃ σ : Equiv.Perm (Fin 24), c ∘ RubikGeometry.lab a b = RubikGeometry.normalTable ∘ σ :=
  @proof_RubikOrbit_reachable_colours
