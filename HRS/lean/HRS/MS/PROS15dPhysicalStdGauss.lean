import HRS.MS.PROS15dPhysicalInfiniteIndep

/-!
# R26-T3.S15d: actual physical isonormal coordinates are an infinite iid standard Gaussian sequence

This upgrades finite-dimensional Gaussian independence to the exact
IsStdGaussianSeq hypothesis required by the S15c infinite Hilbert–Schmidt
Gaussian quadratic tilt. It works for any L2 zero-mean orthonormal spatial
family, including nonsmooth spectral eigenfunctions.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_physical_standard_marginal
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    (I : ProductGaussian μ)
    (e : ℕ → HRS.Euc d → ℝ)
    (he : ∀ i, MemLp (e i) 2 μ)
    (hOrtho : ∀ i j, ∫ x, HRS.Whole.projMean μ (e i) x *
        HRS.Whole.projMean μ (e j) x ∂μ = if i = j then 1 else 0)
    (i : ℕ) :
    I.P.map (I.η (e i)) = gaussianReal 0 1 := by
  letI := I.mΩ
  letI := I.prob
  obtain ⟨v, hLaw⟩ := s15d_physical_centered_gaussian_law I (e i) (he i)
  have hsecond : ∫ ω, I.η (e i) ω ^ 2 ∂I.P = (v : ℝ) :=
    s21g2_s11a_second (I.meas (e i) (he i)).aemeasurable hLaw
  have hcov : ∫ ω, I.η (e i) ω ^ 2 ∂I.P =
      ∫ x, HRS.Whole.projMean μ (e i) x ^ 2 ∂μ := by
    simpa only [pow_two] using I.covariance (e i) (e i) (he i) (he i)
  have hone : ∫ x, HRS.Whole.projMean μ (e i) x ^ 2 ∂μ = 1 := by
    simpa [pow_two] using hOrtho i i
  have hv : (v : ℝ) = 1 := hsecond.symm.trans (hcov.trans hone)
  have hvnn : v = 1 := NNReal.coe_injective hv
  simpa only [hvnn] using hLaw

theorem s15d_physical_standard_gaussian_seq
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    (I : ProductGaussian μ)
    (e : ℕ → HRS.Euc d → ℝ)
    (he : ∀ i, MemLp (e i) 2 μ)
    (hOrtho : ∀ i j, ∫ x, HRS.Whole.projMean μ (e i) x *
        HRS.Whole.projMean μ (e j) x ∂μ = if i = j then 1 else 0) :
    HRS.IsStdGaussianSeq I.P (fun i => I.η (e i)) := by
  letI := I.mΩ
  letI := I.prob
  exact ⟨s15d_physical_infinite_indep_orthogonal I e he hOrtho,
    fun i => s15d_physical_standard_marginal I e he hOrtho i⟩

end HRS.MS.R26T3
