import RubikSTM.Definitions.OBTM.Global.WordCostEnvelope
import RubikSTM.Lemmas.OBTM.DiameterLeUniformWordBound
import RubikSTM.Lemmas.OBTM.GlobalRates.RectangleAggregationHd
set_option autoImplicit false
open Filter Topology RubikCostBridge

theorem proof_RubikOBTM_Global_wordEnvelope_hd (hcost : RubikOBTM.Global.WordCostEnvelope) :
    ∀ η : ℝ, 0 < η → ∃ e : ℕ → ℝ, Tendsto e atTop (nhds 0) ∧ ∃ C : ℝ,
      ∀ᶠ n : ℕ in atTop, (RubikOBTM.obtmDiameter n : ℝ) ≤
        (Real.log (q ^ 2) + η + e n) * m n ^ 2 / (2 * Real.log (m n / h n)) +
          C * (m n ^ 2 / h n + m n) := by
  apply RubikGlobalRates.rectangle_aggregation_hd q (fun n => (RubikOBTM.obtmDiameter n : ℝ)) m h
  · intro n
    dsimp [m,mNat]
    congr 1
    omega
  · intro n
    rfl
  · intro η hη
    obtain ⟨L,ρ,C,Cloc,Cexc,hL,hρ,hC,hloc,hexc,hrate,hfinite⟩ := hcost η hη
    refine ⟨L,ρ,C,Cloc,Cexc,hL,hρ,hC,hloc,hexc,hrate,?_⟩
    filter_upwards [hfinite] with n hn
    obtain ⟨G,r,M,cnt,hbal,harea,hcnt,hM,hword⟩ := hn
    refine ⟨G,r,M,cnt,hbal,harea,hcnt,?_,?_⟩
    · simpa only [RubikCostBridge.block] using hM
    · exact RubikOBTM.diameter_le_uniform_word_bound _ hword
