import RubikSTM.Definitions.OBTM.Band.SlabWord
import RubikSTM.Definitions.OBTM.Finite.PhaseAct
set_option autoImplicit false
open Equiv.Perm
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

theorem proof_RubikOBTMCompiler_native_even_conjugators (p : RubikOBTM.Finite.Phase)
  (g : RubikOBTM.Finite.Intrinsic) (hg : g ∈ RubikOBTM.Finite.nativeC) :
  ∃ σ τ : RubikOBTM.Finite.A,
    σ.val * RubikOBTM.Band.actualSlabPlus^2 * σ.val⁻¹ = (RubikOBTM.Finite.phaseHom p g).1.val ∧
    τ.val * RubikOBTM.Band.actualSlabMinus^2 * τ.val⁻¹ = (RubikOBTM.Finite.phaseHom p g).2.val := by
  let plus : RubikOBTM.Finite.Toggle → Equiv.Perm (Fin 24) := fun v =>
    if v.toAdd.1=0 then (Equiv.swap (0 : Fin 24) 2 * Equiv.swap (0 : Fin 24) 3 * Equiv.swap (1 : Fin 24) 15 * Equiv.swap (5 : Fin 24) 17) else if v.toAdd.2=0 then (Equiv.swap (0 : Fin 24) 2 * Equiv.swap (0 : Fin 24) 4 * Equiv.swap (1 : Fin 24) 15 * Equiv.swap (3 : Fin 24) 17) else (Equiv.swap (3 : Fin 24) 15 * Equiv.swap (5 : Fin 24) 17)
  let minus : RubikOBTM.Finite.Toggle → Equiv.Perm (Fin 24) := fun v =>
    if v.toAdd.1=0 then (Equiv.swap (0 : Fin 24) 3 * Equiv.swap (1 : Fin 24) 16 * Equiv.swap (4 : Fin 24) 13 * Equiv.swap (5 : Fin 24) 19) else if v.toAdd.2=0 then (Equiv.swap (0 : Fin 24) 3 * Equiv.swap (0 : Fin 24) 19 * Equiv.swap (1 : Fin 24) 16 * Equiv.swap (2 : Fin 24) 13) else (Equiv.swap (2 : Fin 24) 3 * Equiv.swap (2 : Fin 24) 16 * Equiv.swap (4 : Fin 24) 13 * Equiv.swap (5 : Fin 24) 19)
  have hp_even : ∀ v, plus v ∈ alternatingGroup (Fin 24) := by
    intro v
    dsimp [plus]
    split_ifs <;> simp [mem_alternatingGroup]
  have hm_even : ∀ v, minus v ∈ alternatingGroup (Fin 24) := by
    intro v
    dsimp [minus]
    split_ifs <;> simp [mem_alternatingGroup]
  have hp : ∀ v : RubikOBTM.Finite.Toggle, v ≠ 1 →
      plus v * RubikOBTM.Band.actualSlabPlus^2 * (plus v)⁻¹ = (RubikOBTM.Finite.base v).val := by
    decide
  have hm : ∀ v : RubikOBTM.Finite.Toggle, v ≠ 1 →
      minus v * RubikOBTM.Band.actualSlabMinus^2 * (minus v)⁻¹ = (RubikOBTM.Finite.base v).val := by
    decide
  have hgn : g.1 ≠ 1 ∧ g.2 ≠ 1 := by simpa [RubikOBTM.Finite.nativeC] using hg
  let σ : RubikOBTM.Finite.A := ⟨plus g.1,hp_even g.1⟩
  let τ : RubikOBTM.Finite.A := ⟨minus g.2,hm_even g.2⟩
  refine ⟨p*σ,p*τ,?_,?_⟩
  · change (p.val * plus g.1) * RubikOBTM.Band.actualSlabPlus^2 * (p.val * plus g.1)⁻¹ =
      p.val * (RubikOBTM.Finite.base g.1).val * p.val⁻¹
    simpa only [mul_inv_rev,mul_assoc] using
      congrArg (fun q : Equiv.Perm (Fin 24) => p.val*q*p.val⁻¹) (hp g.1 hgn.1)
  · change (p.val * minus g.2) * RubikOBTM.Band.actualSlabMinus^2 * (p.val * minus g.2)⁻¹ =
      p.val * (RubikOBTM.Finite.base g.2).val * p.val⁻¹
    simpa only [mul_inv_rev,mul_assoc] using
      congrArg (fun q : Equiv.Perm (Fin 24) => p.val*q*p.val⁻¹) (hm g.2 hgn.2)

#print axioms proof_RubikOBTMCompiler_native_even_conjugators
