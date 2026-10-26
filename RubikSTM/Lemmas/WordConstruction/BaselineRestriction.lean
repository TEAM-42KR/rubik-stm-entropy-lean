import RubikSTM.Proofs.WordConstruction.BaselineRestriction
import Mathlib
set_option autoImplicit false

theorem RubikCompiler.baselineRestriction :
    ∀ {G X : Type*} [Group G] [MulAction G X]
  (Z : G) (S : Set X) (hInv : ∀ x ∈ S, Z • x ∈ S)
  (blocks : List G)
  (hblock : ∀ f ∈ blocks, ∀ x ∈ S, f • x = Z • x), ∀ x ∈ S, blocks.reverse.prod • x = Z ^ blocks.length • x :=
  @proof_RubikCompiler_baselineRestriction
