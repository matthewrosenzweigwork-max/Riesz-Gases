import HRS.MS.S21T4ProdM
import Mathlib.Probability.Distributions.Gaussian.CharFun

/-! R26-T3.S13: Gaussian law identification without changing the probability space. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS

/-- Two centered finite-dimensional Gaussian laws agree when their covariance
quadratic forms agree. This is the law-identification step needed to transfer
the finite-rank CLT to the ONE fixed ProductGaussian space. -/
theorem s21t4_centered_gaussian_law_unique {n : ℕ}
    (γ ν : Measure (EuclideanSpace ℝ (Fin n)))
    (hγ : HRS.IsCenteredGaussian γ) (hν : HRS.IsCenteredGaussian ν)
    (hcov : ∀ L : StrongDual ℝ (EuclideanSpace ℝ (Fin n)),
      covarianceBilinDual γ L L = covarianceBilinDual ν L L) :
    γ = ν := by
  letI : IsGaussian γ := hγ.1
  letI : IsGaussian ν := hν.1
  apply Measure.ext_of_charFunDual
  ext L
  rw [IsGaussian.charFunDual_eq', IsGaussian.charFunDual_eq']
  have hγcomp : ∫ x, L x ∂γ = L (∫ x, id x ∂γ) :=
    ContinuousLinearMap.integral_comp_comm L (IsGaussian.integrable_id (μ := γ))
  have hνcomp : ∫ x, L x ∂ν = L (∫ x, id x ∂ν) :=
    ContinuousLinearMap.integral_comp_comm L (IsGaussian.integrable_id (μ := ν))
  have hmγ : L (∫ x, id x ∂γ) = 0 := hγcomp.symm.trans (hγ.2 L)
  have hmν : L (∫ x, id x ∂ν) = 0 := hνcomp.symm.trans (hν.2 L)
  rw [hmγ, hmν, hcov L]

end HRS.MS.R26T3
