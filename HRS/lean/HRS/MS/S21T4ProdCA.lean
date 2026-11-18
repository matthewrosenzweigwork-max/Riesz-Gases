import HRS.MS.S21T4ProdBZ
import HRS.MS.S21T4ProdBU

/-!
# S13: Gaussian quadratic continuity for two kernels sharing test factors

The same isonormal field is used on both sides. This yields a bound
for the *difference* of quadratic random variables in terms of the
L² difference of their two finite-rank kernels; no independence
between the random variables is asserted or used.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_generic_product_finite_rank_quadratic_same_factors_bound
    (I : ProductGaussian μ) {r : ℕ}
    (c c' : Fin r → Fin r → ℝ) (u : Fin r → Euc d → ℝ)
    (hu : ∀ i, IsR2Test (u i))
    (hc : ∀ i j, c i j = c j i)
    (hc' : ∀ i j, c' i j = c' j i) :
    (∫ ω : I.Ω, (((1 / 2 : ℝ) *
      ∑ i : Fin r, ∑ j : Fin r, c i j *
        (I.η (u i) ω * I.η (u j) ω -
          ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P)) -
      (1 / 2 : ℝ) *
      ∑ i : Fin r, ∑ j : Fin r, c' i j *
        (I.η (u i) ω * I.η (u j) ω -
          ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P)) ^ 2 ∂I.P) ≤
    18 * ∫ z : Euc d × Euc d,
      (r2FiniteRankKernel c u z.1 z.2 -
        r2FiniteRankKernel c' u z.1 z.2) ^ 2 ∂(μ.prod μ) := by
  letI := I.mΩ
  letI := I.prob
  let C : Fin r → Fin r → ℝ := fun i j => c i j - c' i j
  have hC : IsR2FiniteRankData C u :=
    ⟨fun i j => by simp only [C, hc i j, hc' i j],
     (fun i => (hu i).1), (fun i => (hu i).2)⟩
  have hkernel : ∀ x y, r2FiniteRankKernel C u x y =
      r2FiniteRankKernel c u x y - r2FiniteRankKernel c' u x y := by
    intro x y
    simp only [r2FiniteRankKernel, C, sub_mul, Finset.sum_sub_distrib]
  have hQ : ∀ ω : I.Ω,
      (1 / 2 : ℝ) * ∑ i : Fin r, ∑ j : Fin r, C i j *
        (I.η (u i) ω * I.η (u j) ω -
          ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P) =
      ((1 / 2 : ℝ) * ∑ i : Fin r, ∑ j : Fin r, c i j *
        (I.η (u i) ω * I.η (u j) ω -
          ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P)) -
      (1 / 2 : ℝ) * ∑ i : Fin r, ∑ j : Fin r, c' i j *
        (I.η (u i) ω * I.η (u j) ω -
          ∫ ζ, I.η (u i) ζ * I.η (u j) ζ ∂I.P) := by
    intro ω
    simp only [C, sub_mul, Finset.sum_sub_distrib]
    ring
  have hbd := s21t4_generic_product_finite_rank_quadratic_sq_bound I C u hC
  simpa only [hQ, hkernel] using hbd

end HRS.MS.R26T3
