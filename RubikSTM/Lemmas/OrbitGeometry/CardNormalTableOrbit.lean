import RubikSTM.Proofs.OrbitGeometry.CardNormalTableOrbit
import RubikSTM.Definitions.OrbitGeometry.GenPerm
import RubikSTM.Definitions.Channel.Paired.P
set_option autoImplicit false

theorem RubikGeometry.card_normalTable_orbit :
    Nat.card {f : Fin 24 → Rubik.Normal // ∃ σ : Equiv.Perm (Fin 24), f = RubikGeometry.normalTable ∘ σ} = RubikGeometry.orbitColourings :=
  @proof_RubikGeometry_card_normalTable_orbit
