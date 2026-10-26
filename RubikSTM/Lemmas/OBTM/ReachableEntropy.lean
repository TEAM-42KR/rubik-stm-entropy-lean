import RubikSTM.Proofs.OBTM.ReachableEntropy
import RubikSTM.Definitions.OrbitGeometry.GenPerm
set_option autoImplicit false

theorem RubikOBTM.ReachableEntropy :
    ∀ (n : ℕ), RubikGeometry.orbitColourings ^ ((n - 2) / 2 * ((n - 2) / 2 - 1)) ≤ Fintype.card (Rubik.Position n) :=
  @proof_RubikOBTM_ReachableEntropy
