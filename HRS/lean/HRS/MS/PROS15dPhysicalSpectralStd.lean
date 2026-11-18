import HRS.MS.PROS15dPhysicalStdGauss

/-!
# R26-T3.S15d: smoothness-free standard Gaussian spectral eigenfunction family

This directly consumes the R26-T3.S14a spectral theorem's hypotheses:
each eigenfunction belongs to L2_0(μ) and the family is orthonormal
with respect to the unprojected L2 covariance. It proves the exact
IsStdGaussianSeq predicate needed to apply R26-T3.S15c to the ACTUAL
physical Gaussian field, without assuming the eigenfunctions smooth.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_physical_spectral_standard_gaussian_seq
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    (I : ProductGaussian μ)
    (e : ℕ → HRS.Euc d → ℝ)
    (hezero : ∀ i, HRS.Whole.MemL2Zero μ (e i))
    (hon : ∀ i j, ∫ x, e i x * e j x ∂μ =
      if i = j then 1 else 0) :
    HRS.IsStdGaussianSeq I.P (fun i => I.η (e i)) := by
  apply s15d_physical_standard_gaussian_seq I e
    (fun i => (hezero i).1)
  intro i j
  have hi : ∫ x, e i x ∂μ = 0 := (hezero i).2
  have hj : ∫ x, e j x ∂μ = 0 := (hezero j).2
  simpa [HRS.Whole.projMean, HRS.Whole.pair, hi, hj] using hon i j

end HRS.MS.R26T3
