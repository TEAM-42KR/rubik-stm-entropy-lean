import RubikSTM.Proofs.OBTM.Compiler.OutsideRestoration
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.UniversalOwnProfile
set_option autoImplicit false

theorem RubikOBTMCompiler.outside_restoration :
    ∀ {G X : Type*} [Group G] [MulAction G X]
  (Q : G) (hQ : Q^2=1) (S : Set X) (hInv : ∀ x∈S, Q•x∈S)
  (phases : List (List G)) (hblocks : ∀ bs∈phases, ∀ f∈bs, ∀ x∈S, f•x=Q•x)
  (htotal : (phases.map List.length).sum%2=0), ∀ x∈S, (phases.map (fun bs => bs.reverse.prod)).reverse.prod • x=x :=
  @proof_RubikOBTMCompiler_outside_restoration
