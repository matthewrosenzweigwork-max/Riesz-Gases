import HRS.MS.S21T4ProdBS

/-! S13: finite-rank centred Gaussian quadratic form has zero mean for any product probability. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_generic_product_finite_rank_quadratic_mean_zero
    (I : ProductGaussian μ) {r : ℕ}
    (u : Fin r → Euc d → ℝ) (hu : ∀ i, MemLp (u i) 2 μ)
    (c : Fin r → Fin r → ℝ) :
    (∫ ω : I.Ω, (1 / 2 : ℝ) *
      ∑ i : Fin r, ∑ j : Fin r, c i j *
        (I.η (u i) ω * I.η (u j) ω -
          ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P) ∂I.P) = 0 := by
  letI := I.mΩ
  letI := I.prob
  have hz : S94GFam I.P (fun i ω => I.η (u i) ω) :=
    s21l_gfam (s21t4_product_eta_bundle I) hu
  have hi : ∀ i j : Fin r, Integrable
      (fun ω : I.Ω => c i j *
        (I.η (u i) ω * I.η (u j) ω -
          ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P)) I.P := by
    intro i j
    exact ((hz.integrable_zz i j).sub (integrable_const _)).const_mul _
  rw [integral_const_mul, integral_finset_sum _ (fun i _ =>
    integrable_finsetSum _ fun j _ => hi i j)]
  have hz0 : ∀ i j : Fin r,
    ∫ ω, c i j * (I.η (u i) ω * I.η (u j) ω -
      ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P) ∂I.P = 0 := by
    intro i j
    rw [integral_const_mul, integral_sub (hz.integrable_zz i j)
      (integrable_const _), integral_const]
    simp
  simp_rw [integral_finset_sum _ (fun j _ => hi _ j), hz0]
  simp

end HRS.MS.R26T3
