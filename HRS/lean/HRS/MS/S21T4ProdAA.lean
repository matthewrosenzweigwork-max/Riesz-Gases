import HRS.MS.S21T4ProdZ
import HRS.MS.SuppU1

/-! S13: a round-two finite-rank approximation gives actual vanishing L² error. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_round2_approx_integral_sq_zero (s C B : ℝ)
    (hs : 2 * s < (d : ℝ)) (h : Euc d → Euc d → ℝ)
    (hh : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ))
    (hj : ℕ → Euc d → Euc d → ℝ)
    (hA : IsRound2Approx s C B μ h hj) :
    Tendsto (fun j => ∫ z : Euc d × Euc d,
      (hj j z.1 z.2 - h z.1 z.2) ^ 2 ∂(μ.prod μ)) atTop (𝓝 0) := by
  choose m c u hdata heq using hA.finiteRank
  have hjmem : ∀ j, MemLp (fun z : Euc d × Euc d => hj j z.1 z.2) 2
      (μ.prod μ) := by
    intro j
    rw [heq j]
    exact s21t4_finite_rank_memLp (c j) (u j) (hdata j)
  have hdiff : ∀ j, MemLp (fun z : Euc d × Euc d =>
      hj j z.1 z.2 - h z.1 z.2) 2 (μ.prod μ) :=
    fun j => (hjmem j).sub hh
  have hT : Tendsto (fun j => eLpNorm
      (fun z : Euc d × Euc d => hj j z.1 z.2 - h z.1 z.2) 2 (μ.prod μ))
      atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_ofNat] using hA.converges 2 (by norm_num) (by nlinarith)
  exact s21t4_integral_sq_tendsto_zero
    (fun (j : ℕ) (z : Euc d × Euc d) => hj j z.1 z.2 - h z.1 z.2)
    hdiff hT

end HRS.MS.R26T3
