import HRS.MS.S21T4ProdBT

/-! S13: exact linearity of finite-rank Gaussian quadratic forms, including atomic laws. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_generic_product_finite_rank_quadratic_linear
    (I : ProductGaussian μ) {r : ℕ} (u : Fin r → Euc d → ℝ)
    (c c' : Fin r → Fin r → ℝ) (α : ℝ) (ω : I.Ω) :
    (1 / 2 : ℝ) * ∑ i : Fin r, ∑ j : Fin r, (c i j + α * c' i j) *
      (I.η (u i) ω * I.η (u j) ω -
        ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P) =
    ((1 / 2 : ℝ) * ∑ i : Fin r, ∑ j : Fin r, c i j *
      (I.η (u i) ω * I.η (u j) ω -
        ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P)) +
    α * ((1 / 2 : ℝ) * ∑ i : Fin r, ∑ j : Fin r, c' i j *
      (I.η (u i) ω * I.η (u j) ω -
        ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P)) := by
  simp_rw [add_mul, Finset.sum_add_distrib, mul_assoc,
    ← Finset.mul_sum]
  ring

end HRS.MS.R26T3
