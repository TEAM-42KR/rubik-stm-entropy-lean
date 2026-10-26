import RubikSTM.Proofs.WordConstruction.ExteriorCancellation
import Mathlib
set_option autoImplicit false

theorem RubikCompiler.exteriorCancellation :
    ∀ {G X : Type*} [Group G] [MulAction G X]
  (Z : G) (hZ : Z ^ 4 = 1) (S : Set X)
  (hInv : ∀ x ∈ S, Z • x ∈ S) (layers : List (List G))
  (ht : ∀ bs ∈ layers, bs.length % 4 = 1)
  (hblock : ∀ bs ∈ layers, ∀ f ∈ bs, ∀ x ∈ S, f • x = Z • x)
  (hL : layers.length % 4 = 0), ∀ x ∈ S, (layers.map (fun bs => bs.reverse.prod)).reverse.prod • x = x :=
  @proof_RubikCompiler_exteriorCancellation
