import HRS.MS.PROS13CommonFactorApprox
import HRS.MS.PROS13QuadraticChaos
import HRS.MS.PROS13KernelCauchy

/-!
# S13: actual second-chaos Gaussian limits with shared finite-rank factors

An arbitrary finite family of symmetric product-L² kernels is approximated
jointly by one finite set of smooth test functions at each approximation
stage. The Gaussian quadratic random variables all live on the original
ProductGaussian sample space and converge in joint squared L² norm.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_generic_common_factor_gaussian_family
    (I : ProductGaussian μ) {m : ℕ}
    (h : Fin m → Euc d → Euc d → ℝ)
    (hh : ∀ k, MemLp (fun z : Euc d × Euc d => h k z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ k x y, h k x y = h k y x) :
    ∃ (r : ℕ → ℕ)
      (u : (j : ℕ) → Fin (r j) → Euc d → ℝ)
      (c : (j : ℕ) → Fin m → Fin (r j) → Fin (r j) → ℝ)
      (Q : Fin m → I.Ω → ℝ),
      (∀ j a, IsR2Test (u j a)) ∧
      (∀ j k, IsR2FiniteRankData (c j k) (u j)) ∧
      (∀ k, MemLp (Q k) 2 I.P ∧ InSecondChaos I.P I.ξ 3 (Q k)) ∧
      (∀ k, Tendsto
        (fun j => eLpNorm
          (fun z : Euc d × Euc d =>
            r2FiniteRankKernel (c j k) (u j) z.1 z.2 - h k z.1 z.2)
          2 (μ.prod μ)) atTop (𝓝 0)) ∧
      (∀ k, Tendsto
        (fun j : ℕ => ∫ ω : I.Ω,
          (((1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j),
            c j k a b *
              (I.η (u j a) ω * I.η (u j b) ω -
                ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)) -
            Q k ω) ^ 2 ∂I.P) atTop (𝓝 0)) ∧
      Tendsto
        (fun j : ℕ => ∑ k : Fin m,
          ∫ ω : I.Ω,
            (((1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j),
              c j k a b *
                (I.η (u j a) ω * I.η (u j b) ω -
                  ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)) -
              Q k ω) ^ 2 ∂I.P)
        atTop (𝓝 0) := by
  classical
  obtain ⟨r, u, c, htest, hd, hK⟩ :=
    pro_s13_generic_common_factors_approx h hh hs
  have hKm : ∀ k j, MemLp
      (fun z : Euc d × Euc d =>
        r2FiniteRankKernel (c j k) (u j) z.1 z.2)
      2 (μ.prod μ) :=
    fun k j => s21t4_finite_rank_memLp (c j k) (u j) (hd j k)
  have hC : ∀ k : Fin m, ∀ ε : ℝ, 0 < ε →
      ∃ J : ℕ, ∀ a ≥ J, ∀ b ≥ J,
        (∫ z : Euc d × Euc d,
          (r2FiniteRankKernel (c a k) (u a) z.1 z.2 -
            r2FiniteRankKernel (c b k) (u b) z.1 z.2) ^ 2 ∂(μ.prod μ)) < ε := by
    intro k
    exact pro_s13_kernel_cauchy_of_L2_approx
      (h k) (fun j => r2FiniteRankKernel (c j k) (u j))
      (hh k) (hKm k) (hK k)
  have hchoices : ∀ k : Fin m,
      ∃ Q : I.Ω → ℝ, MemLp Q 2 I.P ∧
        Tendsto
          (fun j : ℕ => ∫ ω : I.Ω,
            (((1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j),
              c j k a b *
                (I.η (u j a) ω * I.η (u j b) ω -
                  ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)) -
              Q ω) ^ 2 ∂I.P)
          atTop (𝓝 0) := by
    intro k
    exact pro_s13_gaussian_quadratic_limit_of_kernel_cauchy
      I r (fun j => c j k) u (fun j => hd j k) (hC k)
  choose Q hQ hlim using hchoices
  have hsecond : ∀ k, InSecondChaos I.P I.ξ 3 (Q k) :=
    fun k => pro_s13_quadratic_limit_in_second_chaos
      I r (fun j => c j k) u (fun j => hd j k) (Q k) (hQ k) (hlim k)
  refine ⟨r, u, c, Q, htest, hd, (fun k => ⟨hQ k, hsecond k⟩), hK, hlim, ?_⟩
  have hsum := tendsto_finset_sum (Finset.univ : Finset (Fin m))
    (fun k _ => hlim k)
  simpa using hsum

end HRS.MS.R26T3
