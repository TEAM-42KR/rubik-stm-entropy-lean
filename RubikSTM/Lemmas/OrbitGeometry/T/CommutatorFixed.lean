import RubikSTM.Proofs.OrbitGeometry.T.CommutatorFixed
import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
set_option autoImplicit false
open Rubik

theorem RubikGeometry.T.commutator_fixed :
    ∀ {α : Type*} (O : Set α) (p q : Equiv.Perm α)
    (hp : ∀ s, p s ∈ O ↔ s ∈ O) (hq : ∀ s, q s ∈ O ↔ s ∈ O)
    (hdisj : ∀ s, p s ≠ s → q s ≠ s → s ∈ O) (s : α) (hs : s ∉ O), (p * q * p⁻¹ * q⁻¹) s = s :=
  @proof_RubikGeometry_T_commutator_fixed
