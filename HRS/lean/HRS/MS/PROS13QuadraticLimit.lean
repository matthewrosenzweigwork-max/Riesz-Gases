import HRS.MS.PROS13FamilyMoment
import HRS.Prob.HilbertCLT

/-!
# S13: common-space L² limit of a Cauchy family of Gaussian quadratic forms

The finite-rank kernels may use different smooth test functions and different
ranks. The limit is constructed on the original ProductGaussian sample space.
This gives an actual random variable, not a vacuous orthonormal-basis witness.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_gaussian_quadratic_limit_of_kernel_cauchy
    (I : ProductGaussian μ)
    (r : ℕ → ℕ)
    (c : (j : ℕ) → Fin (r j) → Fin (r j) → ℝ)
    (u : (j : ℕ) → Fin (r j) → Euc d → ℝ)
    (hd : ∀ j, IsR2FiniteRankData (c j) (u j))
    (hC : ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ m ≥ J, ∀ n ≥ J,
      ∫ z : Euc d × Euc d,
        (r2FiniteRankKernel (c m) (u m) z.1 z.2 -
          r2FiniteRankKernel (c n) (u n) z.1 z.2) ^ 2 ∂(μ.prod μ) < ε) :
    ∃ Q : I.Ω → ℝ, MemLp Q 2 I.P ∧
      Tendsto
        (fun j : ℕ => ∫ ω : I.Ω,
          (((1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j), c j a b *
             (I.η (u j a) ω * I.η (u j b) ω -
               ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)) -
            Q ω) ^ 2 ∂I.P)
        atTop (𝓝 0) := by
  letI := I.mΩ
  letI := I.prob
  let Qj : ℕ → I.Ω → ℝ := fun j ω =>
    (1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j), c j a b *
      (I.η (u j a) ω * I.η (u j b) ω -
        ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)
  have hQ2 : ∀ j, MemLp (Qj j) 2 I.P := by
    intro j
    have htest : ∀ i, IsR2Test (u j i) :=
      fun i => ⟨(hd j).smooth i, (hd j).compactSupport i⟩
    have hmem : ∀ i, MemLp (u j i) 2 μ :=
      fun i => (htest i).1.continuous.memLp_of_hasCompactSupport (htest i).2
    exact s21t4_generic_product_finite_rank_quadratic_L2 I (u j) hmem (c j)
  have hQdiff : ∀ m n,
      (∫ ω : I.Ω, (Qj m ω - Qj n ω) ^ 2 ∂I.P) ≤
      18 * ∫ z : Euc d × Euc d,
        (r2FiniteRankKernel (c m) (u m) z.1 z.2 -
          r2FiniteRankKernel (c n) (u n) z.1 z.2) ^ 2 ∂(μ.prod μ) := by
    intro m n
    simpa only [Qj] using
      (s21t4_generic_product_finite_rank_quadratic_distinct_factors_bound
        I (c m) (u m) (c n) (u n) (hd m) (hd n))
  have hcauchy : ∀ ε : ℝ, 0 < ε → ∃ J : ℕ, ∀ m ≥ J, ∀ n ≥ J,
      (∫ ω : I.Ω, ‖Qj m ω - Qj n ω‖ ^ 2 ∂I.P) < ε := by
    intro ε hε
    obtain ⟨J, hJ⟩ := hC (ε / 18) (by positivity)
    refine ⟨J, fun m hm n hn => ?_⟩
    have hkey := hQdiff m n
    have hsmall := hJ m hm n hn
    simpa only [Real.norm_eq_abs, sq_abs] using
      (lt_of_le_of_lt hkey (by nlinarith : 18 *
        (∫ z : Euc d × Euc d,
        (r2FiniteRankKernel (c m) (u m) z.1 z.2 -
          r2FiniteRankKernel (c n) (u n) z.1 z.2) ^ 2 ∂(μ.prod μ)) < ε))
  obtain ⟨Q, hQ, hlim⟩ := HRS.HilbertCLTAux.exists_L2_limit (H := ℝ) hQ2 hcauchy
  refine ⟨Q, hQ, ?_⟩
  simpa only [Qj, Real.norm_eq_abs, sq_abs] using hlim

end HRS.MS.R26T3
