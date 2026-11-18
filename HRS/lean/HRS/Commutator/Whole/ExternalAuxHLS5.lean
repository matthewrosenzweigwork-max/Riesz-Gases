import HRS.Commutator.Whole.ExternalAuxHLS3
import HRS.Commutator.Whole.ExternalAuxHLS4

/-!
# Riesz representation of a Schwartz function (packet X-HLS, part 5)

For a Schwartz `φ` and `g = |∇|^σ φ = 𝓕⁻[(2π|ξ|)^σ 𝓕φ]`: whenever `∫ |z|^{σ-d} |g(x-z)| dz < ∞`,
`c_σ φ(x) = ∫ |z|^{σ-d} g(x-z) dz` (Gaussian subordination, `cmxHLS_riesz_general`).
-/

open MeasureTheory Filter Topology Metric Real Set
open scoped ENNReal NNReal FourierTransform ContDiff

noncomputable section

namespace HRS.Commutator.Whole

variable {d : ℕ}

/-- `|∇|^σ φ = 𝓕⁻[(2π|ξ|)^σ 𝓕φ]` (same expression as `fracS` of `External.lean`). -/
def cmxHLS_frac (σ : ℝ) (φ : SchwartzMap (Euc d) ℂ) (x : Euc d) : ℂ :=
  𝓕⁻ (fun ξ : Euc d => (((2 * Real.pi * ‖ξ‖) ^ σ : ℝ) : ℂ) * 𝓕 (⇑φ) ξ) x

lemma cmxHLS_modulation (F : Euc d → ℂ) (x₀ z : Euc d) :
    𝓕 (fun ξ : Euc d => Complex.exp (((2 * π * inner ℝ ξ x₀ : ℝ) : ℂ) * Complex.I) * F ξ) z
      = 𝓕⁻ F (x₀ - z) := by
  rw [Real.fourier_eq', Real.fourierInv_eq']
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  rw [inner_sub_right]; push_cast; ring

/-- `‖ξ‖^s ‖ψ ξ‖` is integrable for Schwartz `ψ` and `s ≥ 0`. -/
lemma cmxHLS_integrable_rpow_schwartz {s : ℝ} (hs : 0 ≤ s) (ψ : SchwartzMap (Euc d) ℂ) :
    Integrable (fun ξ : Euc d => ‖ξ‖ ^ s * ‖ψ ξ‖) := by
  have h1 : Integrable (fun ξ : Euc d => ‖ψ ξ‖ + ‖ξ‖ ^ ⌈s⌉₊ * ‖ψ ξ‖) :=
    ψ.integrable.norm.add (ψ.integrable_pow_mul volume ⌈s⌉₊)
  refine h1.mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · exact (((Real.continuous_rpow_const hs).comp continuous_norm).mul
      ψ.continuous.norm).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg ξ) s) (norm_nonneg _))]
    have h2 : ‖ξ‖ ^ s ≤ 1 + ‖ξ‖ ^ ⌈s⌉₊ := by
      rcases le_total ‖ξ‖ 1 with h | h
      · have : ‖ξ‖ ^ s ≤ 1 := Real.rpow_le_one (norm_nonneg ξ) h hs
        have : (0 : ℝ) ≤ ‖ξ‖ ^ ⌈s⌉₊ := by positivity
        linarith
      · have : ‖ξ‖ ^ s ≤ ‖ξ‖ ^ (⌈s⌉₊ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h (Nat.le_ceil s)
        rw [Real.rpow_natCast] at this
        linarith
    have h3 := mul_le_mul_of_nonneg_right h2 (norm_nonneg (ψ ξ))
    linarith


/-- Riesz representation: `Γ((d-σ)/2) ∫ |z|^{σ-d} (|∇|^σ φ)(x₀ - z) dz = c φ(x₀)`, under absolute
convergence of the integral. -/
theorem cmxHLS_repr (hd : 1 ≤ d) {σ : ℝ} (hσ : 0 < σ) (hσd : σ < d) (φ : SchwartzMap (Euc d) ℂ)
    (x₀ : Euc d)
    (hfin : Integrable (fun z : Euc d => ‖z‖ ^ (σ - (d : ℝ)) * ‖cmxHLS_frac σ φ (x₀ - z)‖)) :
    ((Real.Gamma (((d : ℝ) - σ) / 2) : ℝ) : ℂ) *
        ∫ z : Euc d, ((‖z‖ ^ (σ - (d : ℝ)) : ℝ) : ℂ) * cmxHLS_frac σ φ (x₀ - z)
      = (((π ^ (((d : ℝ) - σ) - (d : ℝ) / 2) * Real.Gamma (σ / 2) * (2 * π) ^ σ : ℝ)) : ℂ) *
        φ x₀ := by
  set F : Euc d → ℂ := fun ξ => (((2 * Real.pi * ‖ξ‖) ^ σ : ℝ) : ℂ) * 𝓕 (⇑φ) ξ with hF
  set H : Euc d → ℂ := fun ξ => Complex.exp (((2 * π * inner ℝ ξ x₀ : ℝ) : ℂ) * Complex.I) * F ξ
    with hH
  have hγ : 0 < (d : ℝ) - σ := by linarith
  have hγd : (d : ℝ) - σ < d := by linarith
  have hnormF : ∀ ξ : Euc d, ‖F ξ‖ = (2 * π) ^ σ * (‖ξ‖ ^ σ * ‖𝓕 (⇑φ) ξ‖) := by
    intro ξ
    rw [hF]
    show ‖(((2 * Real.pi * ‖ξ‖) ^ σ : ℝ) : ℂ) * 𝓕 (⇑φ) ξ‖ = _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
      Real.mul_rpow (by positivity) (norm_nonneg _)]
    ring
  have hnormH : ∀ ξ : Euc d, ‖H ξ‖ = (2 * π) ^ σ * (‖ξ‖ ^ σ * ‖𝓕 (⇑φ) ξ‖) := by
    intro ξ
    rw [hH]
    show ‖Complex.exp (((2 * π * inner ℝ ξ x₀ : ℝ) : ℂ) * Complex.I) * F ξ‖ = _
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, hnormF]
  have hFc : Continuous F := by
    rw [hF]
    refine Continuous.mul (Complex.continuous_ofReal.comp ?_) (𝓕 φ : SchwartzMap _ ℂ).continuous
    exact (Real.continuous_rpow_const hσ.le).comp (by fun_prop)
  have hHc : Continuous H := by
    rw [hH]
    exact (Complex.continuous_exp.comp (Continuous.mul (Complex.continuous_ofReal.comp
      (by fun_prop)) continuous_const)).mul hFc
  have hHint : Integrable H := by
    have h1 := cmxHLS_integrable_rpow_schwartz hσ.le (𝓕 φ)
    have h2 : Integrable (fun ξ : Euc d => (2 * π) ^ σ * (‖ξ‖ ^ σ * ‖(𝓕 φ : SchwartzMap _ ℂ) ξ‖)) :=
      h1.const_mul _
    refine h2.mono' hHc.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
    rw [hnormH, SchwartzMap.fourier_coe]
  have hR : Integrable (fun ξ : Euc d => ‖ξ‖ ^ (((d : ℝ) - σ) - (d : ℝ)) * ‖H ξ‖) := by
    have h : Integrable (fun ξ : Euc d => (2 * π) ^ σ * ‖𝓕 (⇑φ) ξ‖) := by
      have := ((𝓕 φ : SchwartzMap (Euc d) ℂ).integrable (μ := volume).norm).const_mul ((2 * π) ^ σ)
      simpa [SchwartzMap.fourier_coe] using this
    refine h.congr ?_
    filter_upwards [ae_ne_zero_euc hd] with ξ hξ
    have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    rw [hnormH, show ((d : ℝ) - σ) - (d : ℝ) = -σ by ring, Real.rpow_neg hn.le]
    field_simp
  have hmod : ∀ z : Euc d, 𝓕 H z = cmxHLS_frac σ φ (x₀ - z) := fun z => cmxHLS_modulation F x₀ z
  have hL : Integrable (fun x : Euc d => ‖x‖ ^ (-((d : ℝ) - σ)) * ‖𝓕 H x‖) := by
    refine hfin.congr (Eventually.of_forall fun z => ?_)
    simp only [hmod z, neg_sub]
  have key := cmxHLS_riesz_general hd hγ hγd H hHint hHc.measurable hL hR
  have hlhs : ∫ x : Euc d, ((‖x‖ ^ (-((d : ℝ) - σ)) : ℝ) : ℂ) * 𝓕 H x =
      ∫ z : Euc d, ((‖z‖ ^ (σ - (d : ℝ)) : ℝ) : ℂ) * cmxHLS_frac σ φ (x₀ - z) := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hmod z, neg_sub]
  have hinv : 𝓕⁻ (𝓕 (⇑φ)) x₀ = φ x₀ := by
    have h : (𝓕⁻ (𝓕 φ : SchwartzMap (Euc d) ℂ) : SchwartzMap (Euc d) ℂ) = φ :=
      FourierTransform.fourierInv_fourier_eq φ
    have h2 : (𝓕⁻ (𝓕 φ : SchwartzMap (Euc d) ℂ) : SchwartzMap (Euc d) ℂ) x₀ = φ x₀ := by rw [h]
    rwa [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe] at h2
  have hrhs : ∫ ξ : Euc d, ((‖ξ‖ ^ (((d : ℝ) - σ) - (d : ℝ)) : ℝ) : ℂ) * H ξ =
      (((2 * π) ^ σ : ℝ) : ℂ) * φ x₀ := by
    rw [← hinv, Real.fourierInv_eq', ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_zero_euc hd] with ξ hξ
    have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    rw [hH, hF]
    simp only [smul_eq_mul]
    rw [show ((d : ℝ) - σ) - (d : ℝ) = -σ by ring, Real.rpow_neg hn.le,
      Real.mul_rpow (by positivity) hn.le]
    have hc0 : (((‖ξ‖ ^ σ : ℝ)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hn σ).ne'
    push_cast at hc0 ⊢
    field_simp
  rw [hlhs, hrhs] at key
  have hc : (((π ^ (((d : ℝ) - σ) - (d : ℝ) / 2) * Real.Gamma (σ / 2) * (2 * π) ^ σ : ℝ)) : ℂ) =
      (((π ^ (((d : ℝ) - σ) - (d : ℝ) / 2) * Real.Gamma (((d : ℝ) - ((d : ℝ) - σ)) / 2)) : ℝ) : ℂ) *
        (((2 * π) ^ σ : ℝ) : ℂ) := by
    rw [show ((d : ℝ) - ((d : ℝ) - σ)) / 2 = σ / 2 by ring]
    push_cast
    ring
  rw [hc, mul_assoc, ← key]


lemma cmxHLS_enorm_real_mul {r : ℝ} (hr : 0 ≤ r) (z : ℂ) :
    ‖((r : ℝ) : ℂ) * z‖ₑ = ENNReal.ofReal r * ‖z‖ₑ := by
  rw [enorm_real_mul_eq hr, ENNReal.ofReal_mul hr, ofReal_norm]

lemma cmxHLS_I_measurable (σ : ℝ) {F : Euc d → ℝ≥0∞} (hF : Measurable F) :
    Measurable (cmxHLS_I σ F) := by
  unfold cmxHLS_I
  have : Measurable fun p : Euc d × Euc d => cmxHLS_k σ (p.1 - p.2) * F p.2 := by
    refine Measurable.mul ?_ (hF.comp measurable_snd)
    unfold cmxHLS_k
    exact ((measurable_norm.comp (measurable_fst.sub measurable_snd)).pow_const _).ennreal_ofReal
  exact Measurable.lintegral_prod_right' this

lemma cmxHLS_F_integrable {σ : ℝ} (hσ : 0 < σ) (φ : SchwartzMap (Euc d) ℂ) :
    Integrable (fun ξ : Euc d => (((2 * Real.pi * ‖ξ‖) ^ σ : ℝ) : ℂ) * 𝓕 (⇑φ) ξ) := by
  have h1 := cmxHLS_integrable_rpow_schwartz hσ.le (𝓕 φ)
  have h2 := h1.const_mul ((2 * π) ^ σ)
  have hc : Continuous (fun ξ : Euc d => (((2 * Real.pi * ‖ξ‖) ^ σ : ℝ) : ℂ) * 𝓕 (⇑φ) ξ) := by
    refine Continuous.mul (Complex.continuous_ofReal.comp ?_) (𝓕 φ : SchwartzMap _ ℂ).continuous
    exact (Real.continuous_rpow_const hσ.le).comp (by fun_prop)
  refine h2.mono' hc.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
  show ‖(((2 * Real.pi * ‖ξ‖) ^ σ : ℝ) : ℂ) * 𝓕 (⇑φ) ξ‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    Real.mul_rpow (by positivity) (norm_nonneg _), SchwartzMap.fourier_coe]
  apply le_of_eq
  ring

lemma cmxHLS_frac_continuous {σ : ℝ} (hσ : 0 < σ) (φ : SchwartzMap (Euc d) ℂ) :
    Continuous (cmxHLS_frac σ φ) := by
  have hI := cmxHLS_F_integrable hσ φ
  have hc : Continuous (𝓕 (fun ξ : Euc d => (((2 * Real.pi * ‖ξ‖) ^ σ : ℝ) : ℂ) * 𝓕 (⇑φ) ξ)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hI
  have : cmxHLS_frac σ φ = fun x => 𝓕 (fun ξ : Euc d => (((2 * Real.pi * ‖ξ‖) ^ σ : ℝ) : ℂ) *
      𝓕 (⇑φ) ξ) (-x) := by
    funext x; exact Real.fourierInv_eq_fourier_neg _ _
  rw [this]
  exact hc.comp continuous_neg


/-- **Homogeneous Sobolev inequality** for Schwartz functions, in the exponent conventions of
`hls_sobolev` (`frac` is `|∇|^σ`). -/
theorem cmxHLS_main (hd : 1 ≤ d) (σ : ℝ) (p q : ℝ≥0∞) (hp : 1 < p) (hpq : p < q) (hq : q < ⊤)
    (hσ : 0 < σ) (hrel : q⁻¹ = p⁻¹ - ENNReal.ofReal (σ / d)) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ : SchwartzMap (Euc d) ℂ,
      eLpNorm (⇑φ) q volume ≤ ENNReal.ofReal C * eLpNorm (cmxHLS_frac σ φ) p volume := by
  have hpT : p ≠ ⊤ := (hpq.trans hq).ne
  have hqT : q ≠ ⊤ := hq.ne
  set p' : ℝ := p.toReal with hp'
  set q' : ℝ := q.toReal with hq'
  have hp1 : 1 < p' := by
    have := ENNReal.toReal_strict_mono hpT hp
    simpa using this
  have hpq' : p' < q' := ENNReal.toReal_strict_mono hqT hpq
  have hq0 : 0 < q' := by linarith
  have hp0 : 0 < p' := by linarith
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hrel' : 1 / q' = 1 / p' - σ / d := by
    have hne : p⁻¹ - ENNReal.ofReal (σ / d) ≠ 0 := by
      rw [← hrel]; exact ENNReal.inv_ne_zero.2 hqT
    have hlt : ENNReal.ofReal (σ / d) < p⁻¹ := tsub_pos_iff_lt.1 (pos_iff_ne_zero.2 hne)
    have h1 : p⁻¹ = q⁻¹ + ENNReal.ofReal (σ / d) := by
      rw [hrel]; exact (tsub_add_cancel_of_le hlt.le).symm
    have h2 := congrArg ENNReal.toReal h1
    rw [ENNReal.toReal_add (ENNReal.inv_ne_top.2 (lt_trans zero_lt_one (hp.trans hpq)).ne') ENNReal.ofReal_ne_top,
      ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by positivity)] at h2
    rw [one_div, one_div]
    linarith
  have hσd : σ < d := by
    have h1 : 0 < 1 / q' := by positivity
    have h2 : 1 / p' < 1 := by rw [div_lt_one hp0]; exact hp1
    have : σ / d < 1 := by linarith
    rwa [div_lt_one hdpos] at this
  obtain ⟨C₁, hC₁, hK⟩ := cmxHLS_kernel hd hσ hp1 hpq' hrel'
  set cΓ : ℝ := Real.Gamma (((d : ℝ) - σ) / 2) with hcΓ
  set c0 : ℝ := π ^ (((d : ℝ) - σ) - (d : ℝ) / 2) * Real.Gamma (σ / 2) * (2 * π) ^ σ with hc0
  have hcΓ0 : 0 < cΓ := Real.Gamma_pos_of_pos (by linarith)
  have hc00 : 0 < c0 := by
    have := Real.Gamma_pos_of_pos (by linarith : 0 < σ / 2)
    positivity
  set C₂ : ℝ := cΓ / c0 with hC₂
  have hC₂0 : 0 < C₂ := div_pos hcΓ0 hc00
  refine ⟨C₂ * C₁ ^ (1 / q'), by positivity, fun φ => ?_⟩
  set g : Euc d → ℂ := cmxHLS_frac σ φ with hg
  have hgc : Continuous g := cmxHLS_frac_continuous hσ φ
  set f : Euc d → ℝ≥0 := fun y => ‖g y‖₊ with hf
  have hfm : Measurable f := hgc.nnnorm.measurable
  have hfe : ∀ y, (f y : ℝ≥0∞) = ‖g y‖ₑ := fun y => rfl
  set S : ℝ≥0∞ := ∫⁻ y, (f y : ℝ≥0∞) ^ p' with hS
  have hpne : p ≠ 0 := (lt_trans zero_lt_one hp).ne'
  have hqne : q ≠ 0 := (lt_trans zero_lt_one (hp.trans hpq)).ne'
  have hgp : eLpNorm g p volume = S ^ (1 / p') := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne hpT hgc.aestronglyMeasurable]
    rfl
  have hφq : eLpNorm (⇑φ) q volume = (∫⁻ x, ‖φ x‖ₑ ^ q') ^ (1 / q') :=
    eLpNorm_eq_lintegral_rpow_enorm_toReal hqne hqT φ.continuous.aestronglyMeasurable
  rw [hgp, hφq]
  by_cases hST : S = ⊤
  · rw [hST, ENNReal.top_rpow_of_pos (by positivity), ENNReal.mul_top]
    · exact le_top
    · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hIq := hK f hfm
  have hIm : Measurable (cmxHLS_I σ (fun y => (f y : ℝ≥0∞))) :=
    cmxHLS_I_measurable σ hfm.coe_nnreal_ennreal
  have hIfin : ∫⁻ x, cmxHLS_I σ (fun y => (f y : ℝ≥0∞)) x ^ q' ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hST)) hIq
  have hae : ∀ᵐ x ∂(volume : Measure (Euc d)), cmxHLS_I σ (fun y => (f y : ℝ≥0∞)) x < ⊤ := by
    have := ae_lt_top' (hIm.pow_const q').aemeasurable hIfin
    filter_upwards [this] with x hx
    by_contra h
    rw [not_lt, top_le_iff] at h
    rw [h, ENNReal.top_rpow_of_pos hq0] at hx
    exact lt_irrefl _ hx
  -- pointwise bound
  have hpt : ∀ᵐ x ∂(volume : Measure (Euc d)),
      ‖φ x‖ₑ ≤ ENNReal.ofReal C₂ * cmxHLS_I σ (fun y => (f y : ℝ≥0∞)) x := by
    filter_upwards [hae] with x hx
    have hxI : ∫⁻ z, ENNReal.ofReal (‖z‖ ^ (σ - (d : ℝ))) * (f (x - z) : ℝ≥0∞) =
        cmxHLS_I σ (fun y => (f y : ℝ≥0∞)) x := by
      unfold cmxHLS_I
      rw [← lintegral_sub_left_eq_self (fun y => cmxHLS_k σ (x - y) * (f y : ℝ≥0∞)) x]
      refine lintegral_congr fun z => ?_
      simp only [cmxHLS_k, sub_sub_cancel]
    have hint : Integrable (fun z : Euc d => ‖z‖ ^ (σ - (d : ℝ)) * ‖g (x - z)‖) := by
      refine ⟨?_, ?_⟩
      · exact ((measurable_norm.pow_const _).mul
          (hgc.measurable.comp (measurable_const.sub measurable_id)).norm).aestronglyMeasurable
      · unfold HasFiniteIntegral
        have : ∀ z : Euc d, ‖‖z‖ ^ (σ - (d : ℝ)) * ‖g (x - z)‖‖ₑ =
            ENNReal.ofReal (‖z‖ ^ (σ - (d : ℝ))) * (f (x - z) : ℝ≥0∞) := by
          intro z
          rw [enorm_mul, Real.enorm_of_nonneg (by positivity), enorm_norm, hfe]
        simp_rw [this]
        rw [hxI]; exact hx
    have hrep := cmxHLS_repr hd hσ hσd φ x hint
    set J : ℂ := ∫ z : Euc d, ((‖z‖ ^ (σ - (d : ℝ)) : ℝ) : ℂ) * g (x - z) with hJ
    have h1 : ENNReal.ofReal cΓ * ‖J‖ₑ = ENNReal.ofReal c0 * ‖φ x‖ₑ := by
      have := congrArg (fun w : ℂ => ‖w‖ₑ) hrep
      rw [cmxHLS_enorm_real_mul hcΓ0.le, cmxHLS_enorm_real_mul hc00.le] at this
      exact this
    have h2 : ‖J‖ₑ ≤ cmxHLS_I σ (fun y => (f y : ℝ≥0∞)) x := by
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      rw [← hxI]; refine lintegral_congr fun z => ?_
      rw [cmxHLS_enorm_real_mul (by positivity), hfe]
    calc ‖φ x‖ₑ = ENNReal.ofReal c0⁻¹ * (ENNReal.ofReal c0 * ‖φ x‖ₑ) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hc00.le), inv_mul_cancel₀ hc00.ne',
            ENNReal.ofReal_one, one_mul]
      _ = ENNReal.ofReal c0⁻¹ * (ENNReal.ofReal cΓ * ‖J‖ₑ) := by rw [h1]
      _ ≤ ENNReal.ofReal c0⁻¹ * (ENNReal.ofReal cΓ *
            cmxHLS_I σ (fun y => (f y : ℝ≥0∞)) x) := by gcongr
      _ = ENNReal.ofReal C₂ * cmxHLS_I σ (fun y => (f y : ℝ≥0∞)) x := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hc00.le), hC₂]
          congr 2
          ring
  have hq1 : 0 ≤ 1 / q' := by positivity
  have h1 : ∫⁻ x, ‖φ x‖ₑ ^ q' ≤
      ∫⁻ x, (ENNReal.ofReal C₂ * cmxHLS_I σ (fun y => (f y : ℝ≥0∞)) x) ^ q' :=
    lintegral_mono_ae (hpt.mono fun x hx => ENNReal.rpow_le_rpow hx hq0.le)
  have h2 : ∫⁻ x, (ENNReal.ofReal C₂ * cmxHLS_I σ (fun y => (f y : ℝ≥0∞)) x) ^ q' =
      ENNReal.ofReal C₂ ^ q' * ∫⁻ x, cmxHLS_I σ (fun y => (f y : ℝ≥0∞)) x ^ q' := by
    simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le]
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq0.le ENNReal.ofReal_ne_top)]
  have h3 : ∫⁻ x, ‖φ x‖ₑ ^ q' ≤
      ENNReal.ofReal C₂ ^ q' * (ENNReal.ofReal C₁ * S ^ (q' / p')) :=
    h1.trans (h2.le.trans (mul_le_mul_right hIq _))
  calc (∫⁻ x, ‖φ x‖ₑ ^ q') ^ (1 / q')
      ≤ (ENNReal.ofReal C₂ ^ q' * (ENNReal.ofReal C₁ * S ^ (q' / p'))) ^ (1 / q') :=
        ENNReal.rpow_le_rpow h3 hq1
    _ = ENNReal.ofReal (C₂ * C₁ ^ (1 / q')) * S ^ (1 / p') := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq1, ENNReal.mul_rpow_of_nonneg _ _ hq1,
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one,
          ENNReal.ofReal_mul hC₂0.le, ENNReal.ofReal_rpow_of_pos hC₁ ]
        have : q' / p' * (1 / q') = 1 / p' := by field_simp
        rw [this]
        ring

end HRS.Commutator.Whole
