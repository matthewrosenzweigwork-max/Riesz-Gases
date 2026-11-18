import HRS.MS.PROS13GenericTransferB

/-!
# Generic S13: simultaneous Gaussian quadratic limits are stable across kernels.

The two kernels may be approximated by unrelated finite-rank sequences. Their
actual limiting quadratic chaoses are constructed on the SAME ProductGaussian
space and satisfy a deterministic L² stability estimate. Arbitrary atomic
probability measures are allowed. This removes reliance on a nonempty
infinite orthonormal basis for comparisons of actual quadratic witnesses.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

private theorem pro_s13_integral_sq_triangle
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

/-- An explicit, uniform kernel-L2-to-Gaussian-L2 estimate for two independent
finite-rank constructions of actual quadratic witnesses on the SAME Gaussian
space. No orthonormal basis or nonatomic hypothesis is assumed. -/
theorem pro_s13_generic_two_actual_quadratics_L2_bound
    (I : ProductGaussian μ)
    (h h' : Euc d → Euc d → ℝ)
    (hh : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ))
    (hh' : MemLp (fun z : Euc d × Euc d => h' z.1 z.2) 2 (μ.prod μ))
    (r s : ℕ → ℕ)
    (c : (j : ℕ) → Fin (r j) → Fin (r j) → ℝ)
    (u : (j : ℕ) → Fin (r j) → Euc d → ℝ)
    (c' : (j : ℕ) → Fin (s j) → Fin (s j) → ℝ)
    (v : (j : ℕ) → Fin (s j) → Euc d → ℝ)
    (hd : ∀ j, IsR2FiniteRankData (c j) (u j))
    (hd' : ∀ j, IsR2FiniteRankData (c' j) (v j))
    (Q Q' : I.Ω → ℝ) (hQ : MemLp Q 2 I.P) (hQ' : MemLp Q' 2 I.P)
    (hK : Tendsto (fun j => eLpNorm
      (fun z : Euc d × Euc d =>
        r2FiniteRankKernel (c j) (u j) z.1 z.2 - h z.1 z.2)
      2 (μ.prod μ)) atTop (𝓝 0))
    (hK' : Tendsto (fun j => eLpNorm
      (fun z : Euc d × Euc d =>
        r2FiniteRankKernel (c' j) (v j) z.1 z.2 - h' z.1 z.2)
      2 (μ.prod μ)) atTop (𝓝 0))
    (hlim : Tendsto (fun j : ℕ => ∫ ω : I.Ω,
      (((1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j), c j a b *
          (I.η (u j a) ω * I.η (u j b) ω -
            ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)) -
         Q ω) ^ 2 ∂I.P) atTop (𝓝 0))
    (hlim' : Tendsto (fun j : ℕ => ∫ ω : I.Ω,
      (((1 / 2 : ℝ) * ∑ a : Fin (s j), ∑ b : Fin (s j), c' j a b *
          (I.η (v j a) ω * I.η (v j b) ω -
            ∫ ζ, I.η (v j a) ζ * I.η (v j b) ζ ∂I.P)) -
         Q' ω) ^ 2 ∂I.P) atTop (𝓝 0)) :
    (∫ ω : I.Ω, (Q ω - Q' ω) ^ 2 ∂I.P) ≤
      288 * ∫ z : Euc d × Euc d,
        (h z.1 z.2 - h' z.1 z.2) ^ 2 ∂(μ.prod μ) := by
  letI := I.mΩ
  letI := I.prob
  let K : ℕ → Euc d × Euc d → ℝ := fun j z =>
    r2FiniteRankKernel (c j) (u j) z.1 z.2
  let K' : ℕ → Euc d × Euc d → ℝ := fun j z =>
    r2FiniteRankKernel (c' j) (v j) z.1 z.2
  let F : ℕ → I.Ω → ℝ := fun j ω =>
    (1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j), c j a b *
      (I.η (u j a) ω * I.η (u j b) ω -
        ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)
  let F' : ℕ → I.Ω → ℝ := fun j ω =>
    (1 / 2 : ℝ) * ∑ a : Fin (s j), ∑ b : Fin (s j), c' j a b *
      (I.η (v j a) ω * I.η (v j b) ω -
        ∫ ζ, I.η (v j a) ζ * I.η (v j b) ζ ∂I.P)
  have hKm : ∀ j, MemLp (K j) 2 (μ.prod μ) :=
    fun j => s21t4_finite_rank_memLp (c j) (u j) (hd j)
  have hK'm : ∀ j, MemLp (K' j) 2 (μ.prod μ) :=
    fun j => s21t4_finite_rank_memLp (c' j) (v j) (hd' j)
  have hFm : ∀ j, MemLp (F j) 2 I.P := by
    intro j
    have hu : ∀ a, MemLp (u j a) 2 μ :=
      fun a => ((hd j).smooth a).continuous.memLp_of_hasCompactSupport
        ((hd j).compactSupport a)
    exact s21t4_generic_product_finite_rank_quadratic_L2 I (u j) hu (c j)
  have hF'm : ∀ j, MemLp (F' j) 2 I.P := by
    intro j
    have hv : ∀ a, MemLp (v j a) 2 μ :=
      fun a => ((hd' j).smooth a).continuous.memLp_of_hasCompactSupport
        ((hd' j).compactSupport a)
    exact s21t4_generic_product_finite_rank_quadratic_L2 I (v j) hv (c' j)
  have hKe : Tendsto (fun j => ∫ z : Euc d × Euc d,
      (K j z - h z.1 z.2) ^ 2 ∂(μ.prod μ)) atTop (𝓝 0) := by
    exact s21t4_integral_sq_tendsto_zero
      (fun j z => K j z - h z.1 z.2)
      (fun j => (hKm j).sub hh) (by simpa only [K] using hK)
  have hK'e : Tendsto (fun j => ∫ z : Euc d × Euc d,
      (K' j z - h' z.1 z.2) ^ 2 ∂(μ.prod μ)) atTop (𝓝 0) := by
    exact s21t4_integral_sq_tendsto_zero
      (fun j z => K' j z - h' z.1 z.2)
      (fun j => (hK'm j).sub hh') (by simpa only [K'] using hK')
  have hFe : Tendsto (fun j => ∫ ω : I.Ω,
      (F j ω - Q ω) ^ 2 ∂I.P) atTop (𝓝 0) := by
    simpa only [F] using hlim
  have hF'e : Tendsto (fun j => ∫ ω : I.Ω,
      (F' j ω - Q' ω) ^ 2 ∂I.P) atTop (𝓝 0) := by
    simpa only [F'] using hlim'
  have hfinite : ∀ j,
      (∫ ω : I.Ω, (F j ω - F' j ω) ^ 2 ∂I.P) ≤
      18 * ∫ z : Euc d × Euc d,
        (K j z - K' j z) ^ 2 ∂(μ.prod μ) := by
    intro j
    simpa only [F, F', K, K'] using
      (s21t4_generic_product_finite_rank_quadratic_distinct_factors_bound
        I (c j) (u j) (c' j) (v j) (hd j) (hd' j))
  have hkernel : ∀ j,
      (∫ z : Euc d × Euc d,
        (K j z - K' j z) ^ 2 ∂(μ.prod μ)) ≤
      2 * (∫ z : Euc d × Euc d,
        (K j z - h z.1 z.2) ^ 2 ∂(μ.prod μ)) +
      4 * (∫ z : Euc d × Euc d,
        (h z.1 z.2 - h' z.1 z.2) ^ 2 ∂(μ.prod μ)) +
      4 * (∫ z : Euc d × Euc d,
        (K' j z - h' z.1 z.2) ^ 2 ∂(μ.prod μ)) := by
    intro j
    have ha := pro_s13_integral_sq_triangle
      (K j) (fun z : Euc d × Euc d => h z.1 z.2) (K' j)
      (hKm j) hh (hK'm j)
    have hb := pro_s13_integral_sq_triangle
      (fun z : Euc d × Euc d => h z.1 z.2)
      (fun z : Euc d × Euc d => h' z.1 z.2) (K' j)
      hh hh' (hK'm j)
    have hrev : (∫ z : Euc d × Euc d,
        (h' z.1 z.2 - K' j z) ^ 2 ∂(μ.prod μ)) =
        (∫ z : Euc d × Euc d,
        (K' j z - h' z.1 z.2) ^ 2 ∂(μ.prod μ)) := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by ring
    rw [hrev] at hb
    linarith
  have hgauss : ∀ j,
      (∫ ω : I.Ω, (Q ω - Q' ω) ^ 2 ∂I.P) ≤
      2 * (∫ ω : I.Ω, (F j ω - Q ω) ^ 2 ∂I.P) +
      4 * (∫ ω : I.Ω, (F j ω - F' j ω) ^ 2 ∂I.P) +
      4 * (∫ ω : I.Ω, (F' j ω - Q' ω) ^ 2 ∂I.P) := by
    intro j
    have ha := pro_s13_integral_sq_triangle Q (F j) Q' hQ (hFm j) hQ'
    have hb := pro_s13_integral_sq_triangle (F j) (F' j) Q'
      (hFm j) (hF'm j) hQ'
    have hrev : (∫ ω : I.Ω, (Q ω - F j ω) ^ 2 ∂I.P) =
        (∫ ω : I.Ω, (F j ω - Q ω) ^ 2 ∂I.P) := by
      apply integral_congr_ae
      exact ae_of_all _ fun ω => by ring
    rw [hrev] at ha
    linarith
  have hpoint : ∀ j,
      (∫ ω : I.Ω, (Q ω - Q' ω) ^ 2 ∂I.P) ≤
      288 * (∫ z : Euc d × Euc d,
        (h z.1 z.2 - h' z.1 z.2) ^ 2 ∂(μ.prod μ)) +
      (2 * (∫ ω : I.Ω, (F j ω - Q ω) ^ 2 ∂I.P) +
       144 * (∫ z : Euc d × Euc d,
         (K j z - h z.1 z.2) ^ 2 ∂(μ.prod μ)) +
       288 * (∫ z : Euc d × Euc d,
         (K' j z - h' z.1 z.2) ^ 2 ∂(μ.prod μ)) +
       4 * (∫ ω : I.Ω, (F' j ω - Q' ω) ^ 2 ∂I.P)) := by
    intro j
    have h1 := hgauss j
    have h2 := hfinite j
    have h3 := hkernel j
    linarith
  have herror : Tendsto (fun j =>
      2 * (∫ ω : I.Ω, (F j ω - Q ω) ^ 2 ∂I.P) +
      144 * (∫ z : Euc d × Euc d,
        (K j z - h z.1 z.2) ^ 2 ∂(μ.prod μ)) +
      288 * (∫ z : Euc d × Euc d,
        (K' j z - h' z.1 z.2) ^ 2 ∂(μ.prod μ)) +
      4 * (∫ ω : I.Ω, (F' j ω - Q' ω) ^ 2 ∂I.P))
      atTop (𝓝 0) := by
    have h := (((hFe.const_mul 2).add (hKe.const_mul 144)).add
      (hK'e.const_mul 288)).add (hF'e.const_mul 4)
    simpa only [mul_zero, add_zero, zero_add] using h
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  obtain ⟨j, hj⟩ := (herror.eventually (Iio_mem_nhds hε)).exists
  have hb := hpoint j
  linarith

end HRS.MS.R26T3
