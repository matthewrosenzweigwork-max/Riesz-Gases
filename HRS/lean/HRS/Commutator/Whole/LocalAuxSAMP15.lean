import HRS.Commutator.Whole.LocalAuxSAMP14

/-!
# `K * ⟨∇⟩^α φ = φ - ψ * φ + k * φ` (packet CMX-SAMP, helper file 15)
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff Convolution

noncomputable section

namespace HRS.Commutator.Whole.SAMP1

open HRS HRS.Whole HRS.Commutator.Whole

variable {d : ℕ}

lemma integrable_mul_bdd {f g : Euc d → ℂ} (hf : Integrable f) (hg : Continuous g) {M : ℝ}
    (hM : ∀ x, ‖g x‖ ≤ M) : Integrable (fun x => g x * f x) := by
  refine (hf.norm.const_mul M).mono' (hg.aestronglyMeasurable.mul hf.1)
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)

lemma fourier_bdd {k : Euc d → ℂ} (hk : Integrable k) (ξ : Euc d) : ‖𝓕 k ξ‖ ≤ ∫ x, ‖k x‖ := by
  rw [Real.fourier_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp_rw [Circle.norm_smul]

lemma fourier_continuous' {k : Euc d → ℂ} (hk : Integrable k) : Continuous (𝓕 k) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hk

lemma fourierInv_oneSubChi (φ : SchwartzMap (Euc d) ℂ) (x : Euc d) :
    𝓕⁻ (fun ξ : Euc d => (((1 - chi ξ : ℝ)) : ℂ) * 𝓕 ⇑φ ξ) x =
      φ x - ∫ y, Om d y * φ (x - y) := by
  have hFθ : (⇑(𝓕 φ : SchwartzMap (Euc d) ℂ) : Euc d → ℂ) = 𝓕 ⇑φ := SchwartzMap.fourier_coe φ
  have hΦ : Integrable (𝓕 ⇑φ) := by
    have := (𝓕 φ : SchwartzMap (Euc d) ℂ).integrable (μ := (volume : Measure (Euc d)))
    rwa [hFθ] at this
  have hχΦ : Integrable (fun ξ : Euc d => ((chi ξ : ℝ) : ℂ) * 𝓕 ⇑φ ξ) :=
    integrable_mul_bdd hΦ (Complex.continuous_ofReal.comp cmxFB_chi_contDiff.continuous)
      (M := 1) (fun ξ => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cmxFB_chi_nonneg ξ)]
        exact cmxFB_chi_le_one ξ)
  have e2 : 𝓕⁻ (fun ξ : Euc d => (((1 - chi ξ : ℝ)) : ℂ) * 𝓕 ⇑φ ξ) x =
      𝓕⁻ (𝓕 ⇑φ) x - 𝓕⁻ (fun ξ : Euc d => ((chi ξ : ℝ) : ℂ) * 𝓕 ⇑φ ξ) x := by
    rw [Real.fourierInv_eq', Real.fourierInv_eq', Real.fourierInv_eq',
      ← integral_sub (integrable_inv_phase hΦ x) (integrable_inv_phase hχΦ x)]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  have e3 : 𝓕⁻ (𝓕 ⇑φ) x = φ x := by
    have h : (𝓕⁻ (𝓕 φ : SchwartzMap (Euc d) ℂ) : SchwartzMap (Euc d) ℂ) = φ :=
      FourierTransform.fourierInv_fourier_eq φ
    have h2 := congrArg (fun F : SchwartzMap (Euc d) ℂ => F x) h
    simpa only [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe] using h2
  rw [e2, e3, ← conv_psi_eq]

/-- `K * Bφ = φ - ψ * φ + k * φ`. -/
theorem K_conv_bessel {α : ℝ} {K k : Euc d → ℝ} (hK : Integrable K) (hk : Integrable k)
    (hKF : ∀ ξ : Euc d, 𝓕 (fun x : Euc d => ((K x : ℝ) : ℂ)) ξ =
      (((1 - chi ξ) * (2 * Real.pi * ‖ξ‖) ^ (-α) : ℝ) : ℂ))
    (hkF : ∀ ξ : Euc d,
      (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) * ((1 - chi ξ) * (2 * Real.pi * ‖ξ‖) ^ (-α)) : ℝ) : ℂ) =
        (((1 - chi ξ : ℝ)) : ℂ) + 𝓕 (fun x : Euc d => ((k x : ℝ) : ℂ)) ξ)
    (φ : SchwartzMap (Euc d) ℂ) (x : Euc d) :
    ∫ t, ((K t : ℝ) : ℂ) *
        𝓕⁻ (fun ξ : Euc d => (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) : ℝ) : ℂ) * 𝓕 ⇑φ ξ) (x - t) =
      φ x - (∫ y, Om d y * φ (x - y)) + ∫ y, ((k y : ℝ) : ℂ) * φ (x - y) := by
  have hFφ : (⇑(𝓕 φ : SchwartzMap (Euc d) ℂ) : Euc d → ℂ) = 𝓕 ⇑φ := SchwartzMap.fourier_coe φ
  have hΦ : Integrable (𝓕 ⇑φ) := by
    have := (𝓕 φ : SchwartzMap (Euc d) ℂ).integrable (μ := (volume : Measure (Euc d)))
    rwa [hFφ] at this
  obtain ⟨Sb, hSb⟩ := schwartz_bessel α (𝓕 φ : SchwartzMap (Euc d) ℂ)
  have hSb' : (⇑Sb : Euc d → ℂ) = fun ξ => (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (α / 2) : ℝ) : ℂ) *
      𝓕 ⇑φ ξ := by
    funext ξ; rw [hSb ξ, hFφ]
  have hKc : Integrable (fun x : Euc d => ((K x : ℝ) : ℂ)) := hK.ofReal
  have hkc : Integrable (fun x : Euc d => ((k x : ℝ) : ℂ)) := hk.ofReal
  rw [← hSb']
  have := conv_fourierInv hKc Sb.integrable x
  rw [this]
  -- the symbol
  have hsym : ∀ ξ : Euc d, 𝓕 (fun x : Euc d => ((K x : ℝ) : ℂ)) ξ * Sb ξ =
      (((1 - chi ξ : ℝ)) : ℂ) * 𝓕 ⇑φ ξ + 𝓕 (fun x : Euc d => ((k x : ℝ) : ℂ)) ξ * 𝓕 ⇑φ ξ := by
    intro ξ
    rw [hKF ξ, hSb', ← add_mul, ← hkF ξ]
    push_cast; ring
  have hI1 : Integrable (fun ξ : Euc d => (((1 - chi ξ : ℝ)) : ℂ) * 𝓕 ⇑φ ξ) :=
    integrable_mul_bdd hΦ (Complex.continuous_ofReal.comp
      (continuous_const.sub cmxFB_chi_contDiff.continuous)) (M := 1) (fun ξ => by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [cmxFB_chi_le_one ξ])]
        linarith [cmxFB_chi_nonneg ξ])
  have hI2 : Integrable (fun ξ : Euc d => 𝓕 (fun x : Euc d => ((k x : ℝ) : ℂ)) ξ * 𝓕 ⇑φ ξ) :=
    integrable_mul_bdd hΦ (fourier_continuous' hkc) (M := ∫ x, ‖((k x : ℝ) : ℂ)‖)
      (fun ξ => fourier_bdd hkc ξ)
  simp_rw [hsym]
  have eA : 𝓕⁻ (fun ξ : Euc d => (((1 - chi ξ : ℝ)) : ℂ) * 𝓕 ⇑φ ξ +
      𝓕 (fun x : Euc d => ((k x : ℝ) : ℂ)) ξ * 𝓕 ⇑φ ξ) x =
      𝓕⁻ (fun ξ : Euc d => (((1 - chi ξ : ℝ)) : ℂ) * 𝓕 ⇑φ ξ) x +
        𝓕⁻ (fun ξ : Euc d => 𝓕 (fun x : Euc d => ((k x : ℝ) : ℂ)) ξ * 𝓕 ⇑φ ξ) x := by
    rw [Real.fourierInv_eq', Real.fourierInv_eq', Real.fourierInv_eq',
      ← integral_add (integrable_inv_phase hI1 x) (integrable_inv_phase hI2 x)]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [smul_eq_mul]
    ring
  have e3 : ∀ y : Euc d, 𝓕⁻ (𝓕 ⇑φ) y = φ y := by
    intro y
    have h : (𝓕⁻ (𝓕 φ : SchwartzMap (Euc d) ℂ) : SchwartzMap (Euc d) ℂ) = φ :=
      FourierTransform.fourierInv_fourier_eq φ
    have h2 := congrArg (fun F : SchwartzMap (Euc d) ℂ => F y) h
    simpa only [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe] using h2
  have eB : 𝓕⁻ (fun ξ : Euc d => 𝓕 (fun x : Euc d => ((k x : ℝ) : ℂ)) ξ * 𝓕 ⇑φ ξ) x =
      ∫ y, ((k y : ℝ) : ℂ) * φ (x - y) := by
    have := conv_fourierInv hkc hΦ x
    simp_rw [e3] at this
    exact this.symm
  rw [eA, fourierInv_oneSubChi φ x, eB]

end HRS.Commutator.Whole.SAMP1
