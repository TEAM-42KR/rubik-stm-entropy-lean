import Mathlib
import RubikSTM.Lemmas.Solved.counting_lower_with_offset
set_option autoImplicit false
open Filter Topology

theorem proof_RubikSolved_entropy_of_counting_upper (q a k : ℕ) (hq : 1 ≤ q) (ha : 1 ≤ a) (d : ℕ → ℕ) (u : ℕ → ℝ)
    (hcount : ∀ᶠ n : ℕ in Filter.atTop,
      q ^ ((n - 2) / 2 * ((n - 2) / 2 - 1)) ≤ (a * n + 1) ^ (d n + k))
    (hu : Filter.Tendsto u Filter.atTop (nhds ((1 / 4 : ℝ) * Real.log (q : ℝ))))
    (hle : ∀ᶠ n : ℕ in Filter.atTop,
      (d n : ℝ) * Real.log (n : ℝ) / (n : ℝ)^2 ≤ u n) :
    Filter.Tendsto (fun n : ℕ => (d n : ℝ) * Real.log (n : ℝ) / (n : ℝ)^2)
      Filter.atTop (nhds ((1 / 4 : ℝ) * Real.log (q : ℝ))) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro b hb
    have he : 0 < ((1 / 4 : ℝ) * Real.log (q : ℝ) - b) / 2 := by linarith
    filter_upwards [RubikSolved.counting_lower_with_offset q a k hq ha d hcount _ he]
      with n hn
    linarith
  · intro b hb
    filter_upwards [hle, (tendsto_order.1 hu).2 b hb] with n hn hn'
    exact hn.trans_lt hn'
