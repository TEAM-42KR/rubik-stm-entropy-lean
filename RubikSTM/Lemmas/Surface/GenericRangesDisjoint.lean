import RubikSTM.Proofs.Surface.GenericRangesDisjoint
import RubikSTM.Definitions.Surface.GenericRange
set_option autoImplicit false
open Rubik RubikGeometry RubikGlobal
open scoped Classical

theorem RubikGlobal.generic_ranges_disjoint :
    ∀ {n : ℕ} (p q : RubikGlobal.Q n) (hpq : p ≠ q), Disjoint (RubikGlobal.GenericRange p) (RubikGlobal.GenericRange q) :=
  @proof_RubikGlobal_generic_ranges_disjoint
