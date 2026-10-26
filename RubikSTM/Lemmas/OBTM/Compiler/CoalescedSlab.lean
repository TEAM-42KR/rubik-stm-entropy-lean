import RubikSTM.Proofs.OBTM.Compiler.CoalescedSlab
import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.UniversalOwnProfile
set_option autoImplicit false

theorem RubikOBTMCompiler.coalesced_slab :
    ∀ {G I : Type*} [Group G] (P : I → G) (D : G) (B : List I)
  (hc : ∀ b ∈ B, Commute D (P b)), (B.map (fun b => (P b * D⁻¹)^2)).reverse.prod =
    (B.map (fun b => P b ^ 2)).reverse.prod * (D^2)⁻¹ ^ B.length :=
  @proof_RubikOBTMCompiler_coalesced_slab
