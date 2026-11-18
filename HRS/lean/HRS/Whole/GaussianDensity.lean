import Mathlib

/-!
# Density of polynomial-times-Gaussian functions in `L²`

Auxiliary analytic input for the completeness of the Hermite functions
(`HRS.Whole.hermiteFun_complete`, `HRS.Whole.hermiteFunD_complete`; supplement
`W:eq:euc-oscillator-space`, lines 287-293, "real Hermite basis").

Statement: on a finite-dimensional real inner product space `V` with its Haar (`volume`)
measure, a square-integrable `f` whose moments against `⟪x, ξ⟫^k e^{-‖x‖²/2}` all vanish is
zero almost everywhere.  Coordinate polynomials are linear combinations of the powers
`⟪x, ξ⟫^k` (polarisation), so this is the classical statement that polynomials times the
Gaussian are dense in `L²(V)`.

Proof route (classical; no bibliographic result is used formally): `g = f e^{-‖x‖²/2} ∈ L¹`; its Fourier transform is entire and,
expanding `e^{-2πi⟪x,ξ⟫}` in its power series (dominated convergence with the bound
`|f(x)| e^{-‖x‖²/2 + 2π‖x‖‖ξ‖}`, integrable by Cauchy–Schwarz), vanishes identically;
a function in `L¹` with zero Fourier transform vanishes a.e. (mollify with a normed bump,
`Real.fourier_mul_convolution_eq`/`Continuous.fourierInv_fourier_eq`, and let the bump
shrink).
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform ContDiff RealInnerProductSpace

namespace HRS.Whole



/-- Step 3 -/
theorem ae_eq_zero_of_fourier_eq_zero_aux
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (G : V → ℂ) (hG : Integrable G (volume : Measure V)) (h : ∀ ξ, 𝓕 G ξ = 0) :
    ∀ ψ : SchwartzMap V ℂ, ∫ x, ψ x • G x = 0 := by
  have key : ∀ ψ : SchwartzMap V ℂ, ∫ x, ψ x • G x = 0 := by
    intro ψ
    set ψ' : SchwartzMap V ℂ := 𝓕⁻ ψ with hψ'
    have h1 : ∫ ξ, 𝓕 G ξ • ψ' ξ = ∫ x, G x • 𝓕 (ψ' : V → ℂ) x := by
      simpa using! VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ V) (μ := (volume : Measure V)) (ν := (volume : Measure V))
        Real.continuous_fourierChar continuous_inner hG ψ'.integrable
    simp only [h, zero_smul, integral_zero] at h1
    have h3 : 𝓕 (ψ' : V → ℂ) = ψ := by
      have : 𝓕 (𝓕⁻ ψ) = ψ := FourierInvPair.fourier_fourierInv_eq ψ
      rw [← hψ'] at this
      rw [← SchwartzMap.fourier_coe, this]
    rw [h3] at h1
    simpa [smul_eq_mul, mul_comm] using h1.symm
  exact key

theorem ae_eq_zero_of_fourier_eq_zero_real
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (u : V → ℝ) (hu : Integrable u (volume : Measure V))
    (h : ∀ ξ, 𝓕 (fun x => (u x : ℂ)) ξ = 0) :
    u =ᵐ[volume] 0 := by
  have hG : Integrable (fun x => (u x : ℂ)) (volume : Measure V) := hu.ofReal
  have key := ae_eq_zero_of_fourier_eq_zero_aux _ hG h
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hu.locallyIntegrable
  intro g hg hgc
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  have := key (hg₁.toSchwartzMap hg₂)
  apply Complex.ofReal_injective
  simp only [smul_eq_mul, Complex.ofReal_zero]
  rw [← integral_complex_ofReal]
  simpa [smul_eq_mul] using this

section
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]

theorem integrable_gauss_half :
    Integrable (fun x : V => Real.exp (-(‖x‖ ^ 2 / 2))) (volume : Measure V) := by
  have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := V) (b := (1/2 : ℂ)) (by norm_num) 0 0).norm
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  simp
  rw [← Complex.ofReal_pow, Complex.ofReal_re]; ring

theorem integrable_mul_weight (f : V → ℝ) (hf : MemLp f 2 (volume : Measure V)) (c : ℝ) :
    Integrable (fun x => f x * Real.exp (-(‖x‖ ^ 2 / 2) + c * ‖x‖)) (volume : Measure V) := by
  have hw : Integrable (fun x : V => Real.exp (-(‖x‖ ^ 2 / 2) + c * ‖x‖) ^ 2) (volume : Measure V) := by
    refine ((integrable_gauss_half (V := V)).const_mul (Real.exp (2 * c ^ 2))).mono' ?_ ?_
    · exact (by fun_prop : Continuous fun x : V => Real.exp (-(‖x‖ ^ 2 / 2) + c * ‖x‖) ^ 2).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← Real.exp_nat_mul, ← Real.exp_add]
      apply Real.exp_le_exp.2
      nlinarith [sq_nonneg (‖x‖ - 2 * c)]
  have hf2 := hf.integrable_sq
  refine ((hf2.add hw).div_const 2).mono' ?_ ?_
  · exact hf.aestronglyMeasurable.mul (by fun_prop : Continuous fun x : V => Real.exp (-(‖x‖ ^ 2 / 2) + c * ‖x‖)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    simp only [Pi.add_apply, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    nlinarith [sq_nonneg (|f x| - Real.exp (-(‖x‖ ^ 2 / 2) + c * ‖x‖)), sq_abs (f x)]

theorem fourier_gaussian_moments_eq_zero (f : V → ℝ) (hf : MemLp f 2 (volume : Measure V))
    (h : ∀ (k : ℕ) (ξ : V),
      ∫ x, f x * (inner ℝ x ξ) ^ k * Real.exp (-(‖x‖ ^ 2 / 2)) = 0) (ξ : V) :
    𝓕 (fun x => ((f x * Real.exp (-(‖x‖ ^ 2 / 2)) : ℝ) : ℂ)) ξ = 0 := by
  set G : V → ℂ := fun x => ((f x * Real.exp (-(‖x‖ ^ 2 / 2)) : ℝ) : ℂ) with hG
  set c : ℝ := 2 * Real.pi * ‖ξ‖ with hc
  set z : V → ℂ := fun x => ((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I with hz
  have hzn : ∀ x, ‖z x‖ ≤ c * ‖x‖ := by
    intro x
    simp only [hz, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, hc]
    have := abs_real_inner_le_norm x ξ
    simp only [abs_neg, abs_two, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos, norm_nonneg x, norm_nonneg ξ, mul_le_mul_of_nonneg_left (this) (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
  have hz_meas : Continuous z := by fun_prop
  have hGm : AEStronglyMeasurable G (volume : Measure V) :=
    (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hf.aestronglyMeasurable.mul (by fun_prop : Continuous fun x : V => Real.exp (-(‖x‖ ^ 2 / 2))).aestronglyMeasurable))
  have hbound : Integrable (fun x => ‖G x‖ * Real.exp (c * ‖x‖)) (volume : Measure V) := by
    refine (integrable_mul_weight f hf c).norm.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [hG, Complex.norm_real, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [Real.exp_add]; ring
  -- partial sums
  have hterm : ∀ k : ℕ, Integrable (fun x => (z x) ^ k / (k.factorial : ℂ) * G x) (volume : Measure V) := by
    intro k
    refine hbound.mono' ?_ ?_
    · exact ((hz_meas.pow k).div_const _).aestronglyMeasurable.mul hGm
    · refine Filter.Eventually.of_forall fun x => ?_
      rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
      rw [mul_comm ‖G x‖]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      calc ‖z x‖ ^ k / k.factorial ≤ Real.exp ‖z x‖ := by
            have := Real.sum_le_exp_of_nonneg (norm_nonneg (z x)) (k + 1)
            have h2 : ‖z x‖ ^ k / k.factorial ≤ ∑ i ∈ Finset.range (k+1), ‖z x‖ ^ i / i.factorial :=
              Finset.single_le_sum (f := fun i => ‖z x‖ ^ i / (i.factorial : ℝ)) (fun i _ => by positivity) (Finset.self_mem_range_succ k)
            exact h2.trans this
        _ ≤ Real.exp (c * ‖x‖) := Real.exp_le_exp.2 (hzn x)
  have hzero : ∀ n : ℕ, ∫ x, ∑ k ∈ Finset.range n, (z x) ^ k / (k.factorial : ℂ) * G x = 0 := by
    intro n
    rw [integral_finsetSum _ (fun k _ => hterm k)]
    refine Finset.sum_eq_zero fun k _ => ?_
    have : ∀ x, (z x) ^ k / (k.factorial : ℂ) * G x =
        ((-2 * Real.pi * Complex.I) ^ k / (k.factorial : ℂ)) *
          ((f x * (inner ℝ x ξ) ^ k * Real.exp (-(‖x‖ ^ 2 / 2)) : ℝ) : ℂ) := by
      intro x
      simp only [hz, hG]
      push_cast
      ring
    simp_rw [this]
    rw [integral_const_mul, integral_complex_ofReal, h k ξ]
    simp
  have hlim : Filter.Tendsto (fun n : ℕ => ∫ x, ∑ k ∈ Finset.range n, (z x) ^ k / (k.factorial : ℂ) * G x)
      Filter.atTop (nhds (∫ x, Complex.exp (z x) * G x)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖G x‖ * Real.exp (c * ‖x‖)) ?_ hbound ?_ ?_
    · intro n
      exact (Integrable.aestronglyMeasurable (integrable_finsetSum _ fun k _ => hterm k))
    · intro n
      refine Filter.Eventually.of_forall fun x => ?_
      rw [← Finset.sum_mul, norm_mul, mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      calc ‖∑ k ∈ Finset.range n, (z x) ^ k / (k.factorial : ℂ)‖
          ≤ ∑ k ∈ Finset.range n, ‖(z x) ^ k / (k.factorial : ℂ)‖ := norm_sum_le _ _
        _ = ∑ k ∈ Finset.range n, ‖z x‖ ^ k / k.factorial := by
            simp [norm_pow]
        _ ≤ Real.exp ‖z x‖ := Real.sum_le_exp_of_nonneg (norm_nonneg _) n
        _ ≤ Real.exp (c * ‖x‖) := Real.exp_le_exp.2 (hzn x)
    · refine Filter.Eventually.of_forall fun x => ?_
      simp_rw [← Finset.sum_mul]
      refine Filter.Tendsto.mul_const _ ?_
      have := (NormedSpace.expSeries_div_hasSum_exp (z x)).tendsto_sum_nat
      rwa [← Complex.exp_eq_exp_ℂ] at this
  simp_rw [hzero] at hlim
  have := tendsto_nhds_unique hlim tendsto_const_nhds
  rw [Real.fourier_eq', ← this]
  simp only [smul_eq_mul]
  rfl

end

/-- Polynomials times the Gaussian `e^{-‖x‖²/2}` are dense in `L²(V)`: a square-integrable
function orthogonal to every `⟪x, ξ⟫^k e^{-‖x‖²/2}` vanishes almost everywhere. -/
theorem ae_eq_zero_of_gaussian_moments_eq_zero
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (f : V → ℝ) (hf : MemLp f 2 (volume : Measure V))
    (h : ∀ (k : ℕ) (ξ : V),
      ∫ x, f x * (inner ℝ x ξ) ^ k * Real.exp (-(‖x‖ ^ 2 / 2)) = 0) :
    f =ᵐ[volume] 0 := by
  have hint : Integrable (fun x => f x * Real.exp (-(‖x‖ ^ 2 / 2))) (volume : Measure V) := by
    simpa using integrable_mul_weight f hf 0
  have h0 := ae_eq_zero_of_fourier_eq_zero_real _ hint (fourier_gaussian_moments_eq_zero f hf h)
  filter_upwards [h0] with x hx
  simpa [(Real.exp_pos _).ne'] using hx

end HRS.Whole
