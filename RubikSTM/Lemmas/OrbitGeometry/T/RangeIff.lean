import RubikSTM.Proofs.OrbitGeometry.T.RangeIff
import Mathlib
import RubikSTM.Definitions.OrbitGeometry.GenPerm
set_option autoImplicit false
open Rubik

theorem RubikGeometry.T.range_iff :
    ∀ {α β : Type*} (f : β → α) (p : Equiv.Perm α) (q : Equiv.Perm β)
    (h : ∀ i, p (f i) = f (q i)) (s : α), p s ∈ Set.range f ↔ s ∈ Set.range f :=
  @proof_RubikGeometry_T_range_iff
