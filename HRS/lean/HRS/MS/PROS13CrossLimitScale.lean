import HRS.MS.PROS13CrossLimitLinear

/-!
# Generic S13: homogeneity of the actual product-Gaussian quadratic limit

Scalar multiplication of finite-rank coefficient matrices scales the actual
kernel and centered quadratic Gaussian polynomial exactly; the product-L²
kernel approximation and Gaussian L² limits are preserved for every real
scalar, even when the underlying centered L² space is finite-dimensional.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_actual_product_quadratic_scale
    (I : ProductGaussian μ) (h : Euc d → Euc d → ℝ)
    (Q : I.Ω → ℝ) (hQ : HasActualProductQuadraticLimit I h Q)
    (α : ℝ) :
    HasActualProductQuadraticLimit I
      (fun x y => α * h x y) (fun ω => α * Q ω) := by
  obtain ⟨hm, r, c, u, hd, hK, hlim⟩ := hQ
  letI := I.mΩ
  letI := I.prob
  let cα : (j : ℕ) → Fin (r j) → Fin (r j) → ℝ :=
    fun j a b => α * c j a b
  have hdata : ∀ j, IsR2FiniteRankData (cα j) (u j) := by
    intro j
    refine ⟨?_, (hd j).smooth, (hd j).compactSupport⟩
    intro a b
    simp only [cα]
    rw [(hd j).symm a b]
  have hkernel : ∀ j x y,
      r2FiniteRankKernel (cα j) (u j) x y =
        α * r2FiniteRankKernel (c j) (u j) x y := by
    intro j x y
    simp [r2FiniteRankKernel, cα, Finset.mul_sum, mul_assoc]
  have hgauss : ∀ j (ω : I.Ω),
      (1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j), cα j a b *
        (I.η (u j a) ω * I.η (u j b) ω -
          ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P) =
        α * ((1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j), c j a b *
          (I.η (u j a) ω * I.η (u j b) ω -
            ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)) := by
    intro j ω
    simp [cα, Finset.mul_sum, mul_assoc, mul_left_comm]
  have hknorm : ∀ j, eLpNorm
      (fun z : Euc d × Euc d =>
        r2FiniteRankKernel (cα j) (u j) z.1 z.2 - α * h z.1 z.2)
      2 (μ.prod μ) =
      ‖α‖ₑ * eLpNorm
        (fun z : Euc d × Euc d =>
          r2FiniteRankKernel (c j) (u j) z.1 z.2 - h z.1 z.2)
        2 (μ.prod μ) := by
    intro j
    have heq : (fun z : Euc d × Euc d =>
        r2FiniteRankKernel (cα j) (u j) z.1 z.2 - α * h z.1 z.2) =
        α • (fun z : Euc d × Euc d =>
          r2FiniteRankKernel (c j) (u j) z.1 z.2 - h z.1 z.2) := by
      funext z
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hkernel j z.1 z.2]
      ring
    rw [heq, eLpNorm_const_smul]
  have hKα : Tendsto (fun j => eLpNorm
      (fun z : Euc d × Euc d =>
        r2FiniteRankKernel (cα j) (u j) z.1 z.2 - α * h z.1 z.2)
      2 (μ.prod μ)) atTop (𝓝 0) := by
    have ht := ENNReal.Tendsto.const_mul (a := ‖α‖ₑ) hK
      (Or.inr enorm_ne_top)
    rw [mul_zero] at ht
    simpa only [hknorm] using ht
  have hgaussint : ∀ j, (∫ ω : I.Ω,
      (((1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j), cα j a b *
          (I.η (u j a) ω * I.η (u j b) ω -
            ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)) -
         α * Q ω) ^ 2 ∂I.P) =
      α ^ 2 * (∫ ω : I.Ω,
        (((1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j), c j a b *
          (I.η (u j a) ω * I.η (u j b) ω -
            ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)) -
         Q ω) ^ 2 ∂I.P) := by
    intro j
    have heq : (fun ω : I.Ω =>
        (((1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j), cα j a b *
            (I.η (u j a) ω * I.η (u j b) ω -
              ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)) -
           α * Q ω) ^ 2) =
      (fun ω : I.Ω => α ^ 2 *
        (((1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j), c j a b *
            (I.η (u j a) ω * I.η (u j b) ω -
              ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)) -
           Q ω) ^ 2) := by
      funext ω
      rw [hgauss j ω]
      ring
    rw [heq, integral_const_mul]
  have hlimα : Tendsto (fun j : ℕ => ∫ ω : I.Ω,
      (((1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j), cα j a b *
          (I.η (u j a) ω * I.η (u j b) ω -
            ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)) -
         α * Q ω) ^ 2 ∂I.P) atTop (𝓝 0) := by
    have ht := hlim.const_mul (α ^ 2)
    rw [mul_zero] at ht
    simpa only [hgaussint] using ht
  exact ⟨hm.const_mul α, r, cα, u, hdata, hKα, hlimα⟩

end HRS.MS.R26T3
