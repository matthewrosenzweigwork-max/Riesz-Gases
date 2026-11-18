import HRS.MS.PROS13GenericTransferA
import HRS.MS.PROS13ActualQuadratic
import HRS.MS.S21T4ProdZ

/-!
# Generic quadratic Gaussian L² error against a limiting product-L² kernel

A finite-rank quadratic Gaussian polynomial is controlled directly against
its actual L² limit, not against a zero witness in an empty ONB branch.
The approximation bound is independent of the law and allows atoms.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

private theorem pro_s13_sq_triangle
    {α : Type*} [MeasurableSpace α] {ν : Measure α}
    (f g k : α → ℝ) (hf : MemLp f 2 ν)
    (hg : MemLp g 2 ν) (hk : MemLp k 2 ν) :
    (∫ x, (f x - k x) ^ 2 ∂ν) ≤
      2 * (∫ x, (f x - g x) ^ 2 ∂ν) +
      2 * (∫ x, (g x - k x) ^ 2 ∂ν) := by
  have hd : Integrable (fun x => (f x - k x) ^ 2) ν :=
    (hf.sub hk).integrable_sq
  have hfg : Integrable (fun x => (f x - g x) ^ 2) ν :=
    (hf.sub hg).integrable_sq
  have hgk : Integrable (fun x => (g x - k x) ^ 2) ν :=
    (hg.sub hk).integrable_sq
  have hdom : Integrable (fun x =>
    2 * (f x - g x) ^ 2 + 2 * (g x - k x) ^ 2) ν :=
    (hfg.const_mul 2).add (hgk.const_mul 2)
  have hp : ∀ x, (f x - k x) ^ 2 ≤
    2 * (f x - g x) ^ 2 + 2 * (g x - k x) ^ 2 := by
    intro x
    nlinarith [sq_nonneg ((f x - g x) - (g x - k x))]
  have h := integral_mono hd hdom hp
  rw [integral_add (hfg.const_mul 2) (hgk.const_mul 2),
    integral_const_mul, integral_const_mul] at h
  exact h

theorem pro_s13_generic_gaussian_quadratic_error_bound
    (I : ProductGaussian μ)
    (h : Euc d → Euc d → ℝ)
    (hh : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ))
    (r : ℕ → ℕ)
    (c : (j : ℕ) → Fin (r j) → Fin (r j) → ℝ)
    (u : (j : ℕ) → Fin (r j) → Euc d → ℝ)
    (hd : ∀ j, IsR2FiniteRankData (c j) (u j))
    (Q : I.Ω → ℝ) (hQ : MemLp Q 2 I.P)
    (hK : Tendsto (fun j => eLpNorm
      (fun z : Euc d × Euc d =>
        r2FiniteRankKernel (c j) (u j) z.1 z.2 - h z.1 z.2)
      2 (μ.prod μ)) atTop (𝓝 0))
    (hlim : Tendsto (fun j : ℕ => ∫ ω : I.Ω,
      (((1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j), c j a b *
          (I.η (u j a) ω * I.η (u j b) ω -
            ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)) -
         Q ω) ^ 2 ∂I.P) atTop (𝓝 0)) (j : ℕ) :
    (∫ ω : I.Ω,
      (((1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j), c j a b *
          (I.η (u j a) ω * I.η (u j b) ω -
            ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)) -
         Q ω) ^ 2 ∂I.P) ≤
      72 * ∫ z : Euc d × Euc d,
        (r2FiniteRankKernel (c j) (u j) z.1 z.2 - h z.1 z.2) ^ 2
          ∂(μ.prod μ) := by
  letI := I.mΩ
  letI := I.prob
  let K : ℕ → Euc d × Euc d → ℝ := fun j z =>
    r2FiniteRankKernel (c j) (u j) z.1 z.2
  let F : ℕ → I.Ω → ℝ := fun j ω =>
    (1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j), c j a b *
      (I.η (u j a) ω * I.η (u j b) ω -
        ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)
  have hKm : ∀ j, MemLp (K j) 2 (μ.prod μ) :=
    fun j => s21t4_finite_rank_memLp (c j) (u j) (hd j)
  have hFm : ∀ j, MemLp (F j) 2 I.P := by
    intro j
    have hu : ∀ i, MemLp (u j i) 2 μ :=
      fun i => ((hd j).smooth i).continuous.memLp_of_hasCompactSupport
        ((hd j).compactSupport i)
    exact s21t4_generic_product_finite_rank_quadratic_L2 I (u j) hu (c j)
  have hkT : Tendsto (fun k => ∫ z : Euc d × Euc d,
      (K k z - h z.1 z.2) ^ 2 ∂(μ.prod μ)) atTop (𝓝 0) := by
    exact s21t4_integral_sq_tendsto_zero
      (fun k z => K k z - h z.1 z.2)
      (fun k => (hKm k).sub hh) (by simpa only [K] using hK)
  have hFdiff : ∀ a b,
      (∫ ω : I.Ω, (F a ω - F b ω) ^ 2 ∂I.P) ≤
        18 * ∫ z : Euc d × Euc d, (K a z - K b z) ^ 2 ∂(μ.prod μ) := by
    intro a b
    simpa only [F, K] using
      (s21t4_generic_product_finite_rank_quadratic_distinct_factors_bound
        I (c a) (u a) (c b) (u b) (hd a) (hd b))
  have hpoint : ∀ k,
      (∫ ω : I.Ω, (F j ω - Q ω) ^ 2 ∂I.P) ≤
      72 * (∫ z : Euc d × Euc d, (K j z - h z.1 z.2) ^ 2 ∂(μ.prod μ)) +
      72 * (∫ z : Euc d × Euc d, (K k z - h z.1 z.2) ^ 2 ∂(μ.prod μ)) +
       2 * (∫ ω : I.Ω, (F k ω - Q ω) ^ 2 ∂I.P) := by
    intro k
    have ht := pro_s13_sq_triangle (F j) (F k) Q (hFm j) (hFm k) hQ
    have hk := pro_s13_sq_triangle (K j)
      (fun z : Euc d × Euc d => h z.1 z.2) (K k)
      (hKm j) hh (hKm k)
    have hrev : (∫ z : Euc d × Euc d,
        (h z.1 z.2 - K k z) ^ 2 ∂(μ.prod μ)) =
        (∫ z : Euc d × Euc d,
        (K k z - h z.1 z.2) ^ 2 ∂(μ.prod μ)) := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by ring
    rw [hrev] at hk
    have hf := hFdiff j k
    linarith
  have herror : Tendsto (fun k =>
      72 * (∫ z : Euc d × Euc d,
        (K k z - h z.1 z.2) ^ 2 ∂(μ.prod μ)) +
      2 * (∫ ω : I.Ω, (F k ω - Q ω) ^ 2 ∂I.P))
      atTop (𝓝 0) := by
    have ha := (hkT.const_mul 72).add (hlim.const_mul 2)
    simpa only [K, F, mul_zero, zero_add] using ha
  change (∫ ω, (F j ω - Q ω) ^ 2 ∂I.P) ≤
    72 * ∫ z, (K j z - h z.1 z.2) ^ 2 ∂(μ.prod μ)
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  obtain ⟨k, hk⟩ := (herror.eventually (Iio_mem_nhds hε)).exists
  have := hpoint k
  linarith

end HRS.MS.R26T3
