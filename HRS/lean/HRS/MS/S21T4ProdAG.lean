import HRS.MS.S21T4ProdAF
import Mathlib.Probability.Moments.Covariance

/-! S13: the Gaussian covariance shift matches the canonical Gibbs correction. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_product_covariance_shift (I : ProductGaussian μ)
    (u v : Euc d → ℝ) (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    (∫ ω, I.η u ω * I.η v ω ∂I.P) +
      HRS.Whole.pair μ u * HRS.Whole.pair μ v =
      HRS.Whole.pair μ (fun x => u x * v x) := by
  letI := I.mΩ
  letI := I.prob
  rw [I.covariance u v hu hv]
  change cov[u, v; μ] + (∫ x, u x ∂μ) * (∫ x, v x ∂μ) =
    ∫ x, u x * v x ∂μ
  rw [covariance_eq_sub hu hv]
  simp only [Pi.mul_apply]
  ring

end HRS.MS.R26T3
