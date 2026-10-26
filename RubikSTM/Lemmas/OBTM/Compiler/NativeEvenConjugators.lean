import RubikSTM.Proofs.OBTM.Compiler.NativeEvenConjugators
import RubikSTM.Definitions.OBTM.Band.SlabWord
import RubikSTM.Definitions.OBTM.Finite.PhaseAct
set_option autoImplicit false

theorem RubikOBTMCompiler.native_even_conjugators :
    ∀ (p : RubikOBTM.Finite.Phase)
  (g : RubikOBTM.Finite.Intrinsic) (hg : g ∈ RubikOBTM.Finite.nativeC), ∃ σ τ : RubikOBTM.Finite.A,
    σ.val * RubikOBTM.Band.actualSlabPlus^2 * σ.val⁻¹ = (RubikOBTM.Finite.phaseHom p g).1.val ∧
    τ.val * RubikOBTM.Band.actualSlabMinus^2 * τ.val⁻¹ = (RubikOBTM.Finite.phaseHom p g).2.val :=
  @proof_RubikOBTMCompiler_native_even_conjugators
