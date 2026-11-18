import HRS.MS.S21T4ProdN

/-! S13: uniqueness of pair-space Gaussian laws from their covariance quadratic forms. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

/-- Two centered Gaussian laws on the finite-product vector space for the
finite-rank particle CLT are equal if their covariance forms agree.
This avoids changing to a new Gaussian probability space during transfer. -/
theorem s21t4_gaussian_pair_law_unique {n m : ℕ}
    (γ ν : Measure ((Fin n → ℝ) × (Fin m → ℝ)))
    (hγ : HRS.IsCenteredGaussian γ) (hν : HRS.IsCenteredGaussian ν)
    (hcov : ∀ L : StrongDual ℝ ((Fin n → ℝ) × (Fin m → ℝ)),
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
