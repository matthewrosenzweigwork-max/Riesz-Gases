import HRS.MS.S21T4ProdV
import Mathlib.Analysis.Normed.Lp.SmoothApprox
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T3
open HRS HRS.Whole
variable {d : ℕ}
/-- L² smoothing of product kernels for arbitrary Borel probabilities.
A separated finite-rank approximation is a distinct later step. -/
theorem s21t4_product_kernel_smooth_dense
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (h : Euc d × Euc d → ℝ) (hh : MemLp h 2 (μ.prod μ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : Euc d × Euc d → ℝ,
      HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧
      eLpNorm (h - g) 2 (μ.prod μ) ≤ ENNReal.ofReal ε := by
  exact MeasureTheory.MemLp.exist_eLpNorm_sub_le
    (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) hh hε
end HRS.MS.R26T3
