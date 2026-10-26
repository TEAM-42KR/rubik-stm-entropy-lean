import Mathlib
import RubikSTM.Definitions.Construction.Control.K
import RubikSTM.Lemmas.Construction.Control.CertControlEquation
import RubikSTM.Lemmas.Construction.Control.BaseSwapEquation
import RubikSTM.Lemmas.Construction.Control.AdjacentSwapEquation
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
open RubikConstruction.Control
theorem proof_RubikConstruction_Control_strict_a_only_top : K = ⊤ := by
  have hcontrol (t : ControlIndex) : RubikConstruction.Control.control t ∈ K := Subgroup.subset_closure ⟨t, rfl⟩
  have hc (i : CertIndex) : certPerm i ∈ K := by
    rw [cert_control_equation]
    split
    · exact hcontrol _
    · exact K.inv_mem (hcontrol _)
  have hword (w : List Token) : wordEval w ∈ K := by
    induction w with
    | nil => exact K.one_mem
    | cons t w ih =>
      change tokenPerm t * wordEval w ∈ K
      apply K.mul_mem _ ih
      dsimp only [tokenPerm]
      split
      · exact hc _
      · exact K.inv_mem (hc _)
  have hslice : slice 0 ∈ K := by
    simpa [RubikConstruction.Control.control, facePower] using hcontrol ((fun _ => 0), 0)
  have hbase : baseSwapWitness ∈ K := by
    let H := wordEval path1 * (wordEval path0)⁻¹
    have hH : H ∈ K := K.mul_mem (hword path1) (K.inv_mem (hword path0))
    let T := H * ((certPerm 1)⁻¹ * certPerm 0) * H⁻¹
    have hT : T ∈ K := K.mul_mem
      (K.mul_mem hH (K.mul_mem (K.inv_mem (hc 1)) (hc 0))) (K.inv_mem hH)
    let B := (wordEval pathSwap)⁻¹
    have hB : B ∈ K := K.inv_mem (hword pathSwap)
    change B * (slice 0 * T⁻¹) * B⁻¹ ∈ K
    exact K.mul_mem (K.mul_mem hB (K.mul_mem hslice (K.inv_mem hT))) (K.inv_mem hB)
  rw [base_swap_equation] at hbase
  have hadj (i : Fin 23) : Equiv.swap i.castSucc i.succ ∈ K := by
    rw [← adjacent_swap_equation i]
    exact K.mul_mem (K.mul_mem (hword _) hbase) (K.inv_mem (hword _))
  have hgen : Submonoid.closure
      (Set.range fun i : Fin 23 => Equiv.swap i.castSucc i.succ) ≤ K.toSubmonoid := by
    rw [Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩
    exact hadj i
  rw [Equiv.Perm.mclosure_swap_castSucc_succ 23] at hgen
  apply top_unique
  intro σ _
  exact hgen (by trivial)
