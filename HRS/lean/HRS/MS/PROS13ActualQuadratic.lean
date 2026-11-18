import HRS.MS.PROS13KernelCauchy
import HRS.MS.PROS13SeparatedB

/-!
# S13: an actual Gaussian quadratic limit for every symmetric product-L² kernel

No density or nonatomicity hypothesis on the reference probability measure.
The witness is an L² limit of finite-rank quadratic polynomials on the
original ProductGaussian space, including when centred L² is finite-dimensional.

This does not yet assert the all-basis Wick representation or generic joint CLT.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_generic_actual_quadratic_L2_witness
    (I : ProductGaussian μ)
    (h : Euc d → Euc d → ℝ)
    (hh : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ x y, h x y = h y x) :
    ∃ (r : ℕ → ℕ)
      (c : (j : ℕ) → Fin (r j) → Fin (r j) → ℝ)
      (u : (j : ℕ) → Fin (r j) → Euc d → ℝ)
      (Q : I.Ω → ℝ),
      (∀ j, IsR2FiniteRankData (c j) (u j)) ∧
      Tendsto (fun j => eLpNorm
        (fun z : Euc d × Euc d =>
          r2FiniteRankKernel (c j) (u j) z.1 z.2 - h z.1 z.2)
        2 (μ.prod μ)) atTop (𝓝 0) ∧
      MemLp Q 2 I.P ∧
      Tendsto (fun j : ℕ => ∫ ω : I.Ω,
        (((1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j), c j a b *
          (I.η (u j a) ω * I.η (u j b) ω -
            ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)) -
         Q ω) ^ 2 ∂I.P) atTop (𝓝 0) := by
  classical
  obtain ⟨hj, hjrank, hT⟩ :=
    pro_s13_generic_separated_sequence μ h hh hs
  choose r c u hd heq using hjrank
  have hrank : ∀ j, MemLp
      (fun z : Euc d × Euc d =>
        r2FiniteRankKernel (c j) (u j) z.1 z.2) 2 (μ.prod μ) :=
    fun j => s21t4_finite_rank_memLp (c j) (u j) (hd j)
  have hT' : Tendsto (fun j => eLpNorm
      (fun z : Euc d × Euc d =>
        r2FiniteRankKernel (c j) (u j) z.1 z.2 - h z.1 z.2)
      2 (μ.prod μ)) atTop (𝓝 0) := by
    simpa only [heq] using hT
  have hC := pro_s13_kernel_cauchy_of_L2_approx
      h (fun j => r2FiniteRankKernel (c j) (u j))
      hh hrank hT'
  obtain ⟨Q, hQ, hlim⟩ :=
    pro_s13_gaussian_quadratic_limit_of_kernel_cauchy I r c u hd hC
  exact ⟨r, c, u, Q, hd, hT', hQ, hlim⟩

end HRS.MS.R26T3
