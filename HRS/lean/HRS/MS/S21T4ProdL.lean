import HRS.MS.S21T4ProdK
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-! The missing arbitrary-probability-measure smooth approximation interface for S13. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS.Whole
variable {d : ℕ}

/-- Any L² function under an arbitrary Borel probability measure on Euclidean
space can be approximated by a smooth compactly supported test function.
No absolutely continuous density or lower support bound is assumed. -/
theorem s21t4_product_smooth_dense (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] (f : Euc d → ℝ) (hf : MemLp f 2 μ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : Euc d → ℝ, IsR2Test g ∧
      eLpNorm (f - g) 2 μ ≤ ENNReal.ofReal ε := by
  obtain ⟨g, hc, hs, he⟩ :=
    MeasureTheory.MemLp.exist_eLpNorm_sub_le
      (p := (2 : ℝ≥0∞)) (by simp) (by norm_num) hf hε
  exact ⟨g, ⟨hs, hc⟩, he⟩

end HRS.MS.R26T3
