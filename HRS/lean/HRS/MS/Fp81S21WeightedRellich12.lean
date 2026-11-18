import HRS.MS.Fp81S21WeightedRellich11

/-! The smooth remainder from a spatial cutoff has zero derivatives on the
interior ball.  This is the support fact needed to turn a pointwise weighted
estimate on the exterior into a global weighted-jet estimate. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.FixEq
open Filter Topology

/-- If a function vanishes on the closed ball of radius `ρ`, then every
ordered coordinate derivative vanishes at points whose Japanese bracket is
strictly below `ρ`. -/
theorem fp81s21_weightedRellich_partialDeriv_zero_inner
    {d j : ℕ} {ρ : ℝ} {g : Euc d → ℝ}
    (hzero : ∀ y, ‖y‖ ≤ ρ → g y = 0) {x : Euc d}
    (hx : jbracket x < ρ) (i : Fin j → Fin d) :
    partialDeriv i g x = 0 := by
  have hnorm : ‖x‖ ≤ jbracket x := by
    unfold jbracket
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg ‖x‖])
  have hinner : ‖x‖ < ρ := lt_of_le_of_lt hnorm hx
  have hε : 0 < ρ - ‖x‖ := by linarith
  have heq : g =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [Metric.ball_mem_nhds x hε] with y hy
    have hdist : ‖y - x‖ < ρ - ‖x‖ := by
      simpa [Metric.mem_ball, dist_eq_norm] using hy
    apply hzero y
    calc
      ‖y‖ = ‖(y - x) + x‖ := by congr 1 <;> abel
      _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
      _ ≤ ρ := le_of_lt (by linarith)
  unfold partialDeriv
  rw [(heq.iteratedFDeriv ℝ j).self_of_nhds]
  simp

#print axioms HRS.Fp81.S21.fp81s21_weightedRellich_partialDeriv_zero_inner

end HRS.Fp81.S21
