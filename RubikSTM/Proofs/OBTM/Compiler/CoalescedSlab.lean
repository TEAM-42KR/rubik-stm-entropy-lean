import Mathlib
import RubikSTM.Definitions.OBTM.Compiler.UniversalOwnProfile
set_option autoImplicit false

theorem proof_RubikOBTMCompiler_coalesced_slab {G I : Type*} [Group G] (P : I → G) (D : G) (B : List I)
  (hc : ∀ b ∈ B, Commute D (P b)) :
  (B.map (fun b => (P b * D⁻¹)^2)).reverse.prod =
    (B.map (fun b => P b ^ 2)).reverse.prod * (D^2)⁻¹ ^ B.length := by
  induction B with
  | nil => simp
  | cons b B ih =>
    have hb := hc b (by simp)
    have ht := ih (by intro d hd; exact hc d (by simp [hd]))
    have he : (P b * D⁻¹)^2 = P b^2 * (D^2)⁻¹ := by
      rw [(hb.symm.inv_right).mul_pow,inv_pow]
    have hcomm : Commute ((D^2)⁻¹) (P b^2) := (hb.pow_left 2).inv_left.pow_right 2
    simp only [List.map_cons,List.reverse_cons,List.prod_append,List.prod_singleton,List.length_cons]
    rw [ht,he]
    calc
      (B.map (fun b => P b^2)).reverse.prod * ((D^2)⁻¹)^B.length * (P b^2 * (D^2)⁻¹) =
          (B.map (fun b => P b^2)).reverse.prod * (((D^2)⁻¹)^B.length * P b^2) * (D^2)⁻¹ := by
            simp only [mul_assoc]
      _ = (B.map (fun b => P b^2)).reverse.prod * (P b^2 * ((D^2)⁻¹)^B.length) * (D^2)⁻¹ := by
        rw [(hcomm.pow_left _).eq]
      _ = ((B.map (fun b => P b^2)).reverse.prod * P b^2) * ((D^2)⁻¹)^(B.length+1) := by
        simp [pow_succ,mul_assoc]

#print axioms proof_RubikOBTMCompiler_coalesced_slab
