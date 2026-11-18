import HRS.MS.PROS13CrossL2Sum

/-!
# Generic S13: sum of unrelated product-L² kernel approximations

Uses the L² Minkowski inequality; no nonatomicity or common finite-rank
factor family is assumed.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos

variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_kernel_approximation_add
    (K K' : ℕ → Euc d → Euc d → ℝ)
    (h h' : Euc d → Euc d → ℝ)
    (hK : Tendsto (fun j => eLpNorm
      (fun z : Euc d × Euc d => K j z.1 z.2 - h z.1 z.2)
      2 (μ.prod μ)) atTop (𝓝 0))
    (hK' : Tendsto (fun j => eLpNorm
      (fun z : Euc d × Euc d => K' j z.1 z.2 - h' z.1 z.2)
      2 (μ.prod μ)) atTop (𝓝 0)) :
    Tendsto (fun j => eLpNorm
      (fun z : Euc d × Euc d =>
        (K j z.1 z.2 + K' j z.1 z.2) -
        (h z.1 z.2 + h' z.1 z.2))
      2 (μ.prod μ)) atTop (𝓝 0) := by
  have hsum := hK.add hK'
  simp only [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hsum (fun _ => bot_le) fun j => ?_
  have heq : (fun z : Euc d × Euc d =>
        (K j z.1 z.2 + K' j z.1 z.2) -
        (h z.1 z.2 + h' z.1 z.2)) =
      (fun z : Euc d × Euc d => K j z.1 z.2 - h z.1 z.2) +
      (fun z : Euc d × Euc d => K' j z.1 z.2 - h' z.1 z.2) := by
    funext z
    simp only [Pi.add_apply]
    ring
  rw [heq]
  exact eLpNorm_add_le (by norm_num)

end HRS.MS.R26T3
