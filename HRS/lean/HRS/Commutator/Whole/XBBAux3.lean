import HRS.Commutator.Whole.XBBAux2

/-!
# Packet XBB, part 3: Kato–Ponce pair estimates (scale `1`) from the X-LI fractional Leibniz rule

* `xbb_bernstein`: `‖J^β f‖_∞ ≲ ‖f‖_∞` for `f` Fourier-supported in `|ξ| ≤ 4`;
* `xbb_bessel_hom`: `‖J^β f‖_p ≲ ‖|∇|^β f‖_p` for `f` Fourier-supported in `|ξ| ≥ 2`;
* `xbb_sobolev`: `‖Γ‖_{2d/(d-2β)} ≲ ‖Γ‖_{Ḣ^β}`;
* `xbb_pair_low`, `xbb_pair_high`: the Leibniz estimate for `f Γ` in `Ḣ^β`.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section
namespace HRS.Commutator.Whole.XBB
open HRS.Commutator.Whole HRS.Commutator.Whole.XLI HRS.Commutator.Whole.XNRS
variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- `G` is a companion of `f`: `𝓕 G = (2π|ξ|)^β 𝓕 f` (a realisation of `|∇|^β f`). -/
def XComp (β : ℝ) (f G : 𝓢(𝔼, ℂ)) : Prop :=
  ∀ ξ : 𝔼, 𝓕 (⇑G) ξ = (((2 * Real.pi * ‖ξ‖) ^ β : ℝ) : ℂ) * 𝓕 (⇑f) ξ

/-- the symbol of the Bessel multiplier cut off at frequency `4` -/
def xbbThB (β : ℝ) (ξ : 𝔼) : ℂ := bsymX β ξ * cutC (((2 : ℝ) ^ (2 : ℤ))⁻¹ • ξ)

lemma xbbThB_contDiff (β : ℝ) : ContDiff ℝ ∞ (xbbThB β : 𝔼 → ℂ) :=
  (bsymX_temperate β).1.mul (cutC_contDiff.comp (contDiff_const_smul _))

lemma xbbThB_cs (β : ℝ) : HasCompactSupport (xbbThB β : 𝔼 → ℂ) :=
  (symbol_cs cutC_cs 2).mul_left

lemma xbb_Fm_eq_cv (β : ℝ) (f : 𝓢(𝔼, ℂ)) (hf : ∀ ξ : 𝔼, 4 < ‖ξ‖ → 𝓕 (⇑f) ξ = 0) :
    ⇑(Fm β f) = cv (symK (xbbThB β) 0) ⇑f := by
  rw [cv_symK_eq_mulS (xbbThB_contDiff β) (xbbThB_cs β) f 0]
  congr 1
  refine xschwartz_ext_fourier fun ξ => ?_
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe]
  unfold Fm
  rw [fourier_mulS, fourier_mulS]
  by_cases h : 4 < ‖ξ‖
  · rw [hf ξ h]; simp
  · push Not at h
    have hc : cutC (((2 : ℝ) ^ (2 : ℤ))⁻¹ • ξ) = 1 := by
      refine cutC_eq_one_of_le ?_
      rw [norm_smul, norm_inv]
      norm_num
      linarith
    simp only [xbbThB, zpow_zero, inv_one, one_smul, hc, mul_one]

lemma xbb_bernstein (β : ℝ) : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : 𝓢(𝔼, ℂ),
    (∀ ξ : 𝔼, 4 < ‖ξ‖ → 𝓕 (⇑f) ξ = 0) → ∀ B : ℝ, 0 ≤ B → (∀ x, ‖f x‖ ≤ B) →
      eLpNorm (⇑(Fm β f)) ⊤ volume ≤ C * ENNReal.ofReal B := by
  refine ⟨∫⁻ z : 𝔼, ‖symK (xbbThB β) 0 z‖ₑ, (symK_integrable (xbbThB_contDiff β) (xbbThB_cs β) 0).hasFiniteIntegral.ne, ?_⟩
  intro f hf B hB hfB
  rw [xbb_Fm_eq_cv β f hf]
  refine (eLpNorm_cv_le (symK_continuous (xbbThB_contDiff β) (xbbThB_cs β) 0).measurable
    f.continuous.measurable le_top).trans ?_
  gcongr
  rw [eLpNorm_exponent_top]
  · exact eLpNormEssSup_le_of_ae_bound (Eventually.of_forall hfB)
  · exact f.continuous.aestronglyMeasurable


lemma xbb_eq_of_fourier_eq {F₁ F₂ : 𝔼 → ℂ} (h1 : Integrable F₁) (h2 : Integrable F₂)
    (c1 : Continuous F₁) (c2 : Continuous F₂) (hF : ∀ ξ, 𝓕 F₁ ξ = 𝓕 F₂ ξ)
    (hi : Integrable (𝓕 F₁)) : F₁ = F₂ := by
  have hF' : 𝓕 F₁ = 𝓕 F₂ := funext hF
  funext x
  have e1 := Integrable.fourierInv_fourier_eq h1 hi c1.continuousAt (v := x)
  have e2 := Integrable.fourierInv_fourier_eq h2 (hF' ▸ hi) c2.continuousAt (v := x)
  rw [← e1, ← e2, hF']

/-- the Bessel multiplier is controlled by the homogeneous one in every `L^p`, `p ≥ 1`, at high
frequencies -/
lemma xbb_bessel_hom (hd : 3 ≤ d) {β : ℝ} (hβ : 0 < β) (hβd : β < d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (f G : 𝓢(𝔼, ℂ)), XComp β f G → (∀ ξ : 𝔼, ‖ξ‖ < 2 → 𝓕 (⇑f) ξ = 0) →
      ∀ p : ℝ≥0∞, 1 ≤ p → eLpNorm (⇑(Fm β f)) p volume ≤ C * eLpNorm (⇑G) p volume := by
  obtain ⟨k, hk, hkF⟩ := cmxMY_mult_kernel_bessel hd β hβ hβd
  obtain ⟨g, hgm, hkg⟩ := hk.aestronglyMeasurable
  set kC : 𝔼 → ℂ := fun x => ((g x : ℝ) : ℂ) with hkC
  have hkCm : Measurable kC := Complex.measurable_ofReal.comp hgm.measurable
  have hkCi : Integrable kC := by
    have : Integrable (fun x => ((k x : ℝ) : ℂ)) := hk.ofReal
    exact this.congr (hkg.mono fun x hx => by simp [hkC, hx])
  have hFk : ∀ ξ : 𝔼, 𝓕 kC ξ = 𝓕 (fun x : 𝔼 => ((k x : ℝ) : ℂ)) ξ := by
    intro ξ
    simp only [Real.fourier_eq]
    refine integral_congr_ae (hkg.mono fun x hx => ?_)
    simp [hkC, hx]
  refine ⟨1 + ∫⁻ z, ‖kC z‖ₑ, ?_, ?_⟩
  · exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hkCi.hasFiniteIntegral.ne⟩
  intro f G hG hf p hp
  have hcvi : Integrable (cv kC ⇑G) :=
    Integrable.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hkCi G.integrable
  have hcvc : Continuous (cv kC ⇑G) := by
    refine BddAbove.continuous_convolution_right_of_integrable (ContinuousLinearMap.mul ℂ ℂ) ?_
      hkCi G.continuous
    obtain ⟨B, -, hB⟩ := G.decay 0 0
    exact ⟨B, by rintro _ ⟨y, rfl⟩; simpa using hB y⟩
  have hF2i : Integrable (fun x => G x + cv kC ⇑G x) := G.integrable.add hcvi
  have hFT : ∀ ξ : 𝔼, 𝓕 (⇑(Fm β f)) ξ = 𝓕 (fun x => G x + cv kC ⇑G x) ξ := by
    intro ξ
    have e1 : 𝓕 (fun x => G x + cv kC ⇑G x) ξ = 𝓕 ⇑G ξ + 𝓕 kC ξ * 𝓕 ⇑G ξ := by
      rw [xbb_fourier_add G.integrable hcvi]
      congr 1
      exact Real.fourier_mul_convolution_eq hkCi G.integrable ξ
    rw [e1, hFk ξ]
    unfold Fm
    rw [fourier_mulS, hG ξ]
    by_cases h2 : ‖ξ‖ < 2
    · simp [hf ξ h2]
    · push Not at h2
      have hchi : chi ξ = 0 := cmxFB_chi_zero h2
      have hkξ := hkF ξ
      rw [hchi] at hkξ
      have hw : 0 < 2 * Real.pi * ‖ξ‖ := by
        have : 0 < ‖ξ‖ := by linarith
        positivity
      have hwB : (2 * Real.pi * ‖ξ‖) ^ β * (2 * Real.pi * ‖ξ‖) ^ (-β) = 1 := by
        rw [← Real.rpow_add hw]; simp
      have hAB : (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (β / 2) : ℝ) : ℂ) *
          (((2 * Real.pi * ‖ξ‖) ^ (-β) : ℝ) : ℂ) = 1 + 𝓕 (fun x : 𝔼 => ((k x : ℝ) : ℂ)) ξ := by
        have := hkξ
        push_cast at this ⊢
        simpa using this
      have hwBC : (((2 * Real.pi * ‖ξ‖) ^ β : ℝ) : ℂ) * (((2 * Real.pi * ‖ξ‖) ^ (-β) : ℝ) : ℂ) = 1 := by
        exact_mod_cast hwB
      unfold bsymX
      calc (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (β / 2) : ℝ) : ℂ) * 𝓕 (⇑f) ξ
          = (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (β / 2) : ℝ) : ℂ) *
            ((((2 * Real.pi * ‖ξ‖) ^ (-β) : ℝ) : ℂ) * (((2 * Real.pi * ‖ξ‖) ^ β : ℝ) : ℂ)) * 𝓕 (⇑f) ξ := by
            rw [mul_comm (((2 * Real.pi * ‖ξ‖) ^ (-β) : ℝ) : ℂ), hwBC]; ring
        _ = (((((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (β / 2) : ℝ) : ℂ) *
            (((2 * Real.pi * ‖ξ‖) ^ (-β) : ℝ) : ℂ))) * ((((2 * Real.pi * ‖ξ‖) ^ β : ℝ) : ℂ) * 𝓕 (⇑f) ξ) := by
            ring
        _ = _ := by rw [hAB]; ring
  have hmain : ⇑(Fm β f) = fun x => G x + cv kC ⇑G x :=
    xbb_eq_of_fourier_eq (Fm β f).integrable hF2i (Fm β f).continuous
      (G.continuous.add hcvc) hFT (by rw [← SchwartzMap.fourier_coe]; exact (𝓕 (Fm β f)).integrable)
  rw [hmain]
  have hpm : AEStronglyMeasurable (⇑G) volume := G.continuous.aestronglyMeasurable
  have hcm : AEStronglyMeasurable (cv kC ⇑G) volume := hcvc.aestronglyMeasurable
  calc eLpNorm (fun x => G x + cv kC ⇑G x) p volume
      ≤ eLpNorm (⇑G) p volume + eLpNorm (cv kC ⇑G) p volume := eLpNorm_add_le hp
    _ ≤ eLpNorm (⇑G) p volume + (∫⁻ z, ‖kC z‖ₑ) * eLpNorm (⇑G) p volume := by
        gcongr
        exact eLpNorm_cv_le hkCm G.continuous.measurable hp
    _ = _ := by ring


lemma xbb_norm_bsymX (β : ℝ) (ξ : 𝔼) : ‖bsymX β ξ‖ = (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (β / 2) := by
  unfold bsymX
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]

lemma xbb_fourier_Fm (β : ℝ) (h : 𝓢(𝔼, ℂ)) (ξ : 𝔼) :
    𝓕 (⇑(Fm β h)) ξ = bsymX β ξ * 𝓕 (⇑h) ξ := by
  unfold Fm; rw [fourier_mulS]

/-- `‖h‖_{Ḣ^β} ≤ ‖J^β h‖_{L²}` -/
lemma xbbN_le_Fm {β : ℝ} (hβ : 0 ≤ β) (h : 𝓢(𝔼, ℂ)) :
    xbbN β ⇑h ≤ eLpNorm (⇑(Fm β h)) 2 volume := by
  rw [xbb_eLpNorm_two_eq]
  have := xbbN_mono_fourier (β₁ := β) (β₂ := 0) (u := ⇑h) (v := ⇑(Fm β h)) (C := 1) zero_le_one
    (fun ξ => by
      rw [xbb_fourier_Fm, norm_mul, xbb_norm_bsymX, Real.rpow_zero, one_mul, one_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have h1 : 2 * Real.pi * ‖ξ‖ = ((2 * Real.pi * ‖ξ‖) ^ 2) ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
      calc (2 * Real.pi * ‖ξ‖) ^ β = (((2 * Real.pi * ‖ξ‖) ^ 2) ^ ((1 : ℝ) / 2)) ^ β := by rw [← h1]
        _ = ((2 * Real.pi * ‖ξ‖) ^ 2) ^ (β / 2) := by
            rw [← Real.rpow_mul (by positivity)]; congr 1; ring
        _ ≤ (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (β / 2) := by
            refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
            nlinarith [sq_nonneg (Real.pi * ‖ξ‖)])
  simpa using this

/-- `‖J^β Γ‖_{L²} ≲ ‖Γ‖_{Ḣ^β}` for `Γ` supported at frequencies `≥ 1` -/
lemma eLpNorm_Fm_le {β : ℝ} (hβ : 0 ≤ β) (Γ : 𝓢(𝔼, ℂ)) (hΓ : ∀ ξ : 𝔼, ‖ξ‖ < 1 → 𝓕 (⇑Γ) ξ = 0) :
    eLpNorm (⇑(Fm β Γ)) 2 volume ≤ ENNReal.ofReal ((1 + 1 / (4 * Real.pi ^ 2)) ^ (β / 2)) * xbbN β ⇑Γ := by
  rw [xbb_eLpNorm_two_eq]
  refine xbbN_mono_fourier (β₁ := 0) (β₂ := β) (by positivity) (fun ξ => ?_)
  rw [xbb_fourier_Fm, norm_mul, xbb_norm_bsymX, Real.rpow_zero, one_mul]
  by_cases h : ‖ξ‖ < 1
  · simp [hΓ ξ h]
  · push Not at h
    rw [← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    have hp : 0 < Real.pi := Real.pi_pos
    calc (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (β / 2)
        ≤ (((1 + 1 / (4 * Real.pi ^ 2)) * (2 * Real.pi * ‖ξ‖) ^ 2)) ^ (β / 2) := by
          refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
          have h1 : 1 ≤ ‖ξ‖ ^ 2 := by nlinarith
          have : (1 + 1 / (4 * Real.pi ^ 2)) * (2 * Real.pi * ‖ξ‖) ^ 2 = 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 + ‖ξ‖ ^ 2 := by
            field_simp; ring
          rw [this]; linarith
      _ = (1 + 1 / (4 * Real.pi ^ 2)) ^ (β / 2) * (2 * Real.pi * ‖ξ‖) ^ β := by
          have e : ((2 * Real.pi * ‖ξ‖) ^ 2) ^ (β / 2) = (2 * Real.pi * ‖ξ‖) ^ β := by
            rw [← Real.rpow_natCast (2 * Real.pi * ‖ξ‖) 2, ← Real.rpow_mul (by positivity)]
            congr 1; push_cast; ring
          rw [Real.mul_rpow (by positivity) (by positivity), e]

/-- `‖Γ‖_{L²} ≲ ‖Γ‖_{Ḣ^β}` for `Γ` supported at frequencies `≥ 1` -/
lemma eLpNorm_two_le_xbbN {β : ℝ} (hβ : 0 ≤ β) (Γ : 𝓢(𝔼, ℂ)) (hΓ : ∀ ξ : 𝔼, ‖ξ‖ < 1 → 𝓕 (⇑Γ) ξ = 0) :
    eLpNorm (⇑Γ) 2 volume ≤ ENNReal.ofReal ((2 * Real.pi) ^ (-β)) * xbbN β ⇑Γ := by
  rw [xbb_eLpNorm_two_eq]
  refine xbbN_mono_fourier (β₁ := 0) (β₂ := β) (by positivity) (fun ξ => ?_)
  rw [Real.rpow_zero, one_mul]
  by_cases h : ‖ξ‖ < 1
  · simp [hΓ ξ h]
  · push Not at h
    have hp : 0 < Real.pi := Real.pi_pos
    have h1 : (2 * Real.pi) ^ β ≤ (2 * Real.pi * ‖ξ‖) ^ β :=
      Real.rpow_le_rpow (by positivity) (by nlinarith) hβ
    have h2 : (2 * Real.pi) ^ (-β) * (2 * Real.pi) ^ β = 1 := by
      rw [← Real.rpow_add (by positivity)]; simp
    have h3 : 1 ≤ (2 * Real.pi) ^ (-β) * (2 * Real.pi * ‖ξ‖) ^ β := by
      calc (1 : ℝ) = (2 * Real.pi) ^ (-β) * (2 * Real.pi) ^ β := h2.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
    calc ‖𝓕 (⇑Γ) ξ‖ = 1 * ‖𝓕 (⇑Γ) ξ‖ := (one_mul _).symm
      _ ≤ ((2 * Real.pi) ^ (-β) * (2 * Real.pi * ‖ξ‖) ^ β) * ‖𝓕 (⇑Γ) ξ‖ :=
          mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      _ = _ := by ring


/-- exponent of the Sobolev embedding `Ḣ^β ⊂ L^{2d/(d-2β)}` -/
def xbbQ1 (d : ℕ) (β : ℝ) : ℝ≥0∞ := ENNReal.ofReal (2 * d / (d - 2 * β))

lemma xbb_sobolev (hd : 1 ≤ d) {β : ℝ} (hβ : 0 < β) (hβd : 2 * β < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Γ G : 𝓢(𝔼, ℂ)), XComp β Γ G →
      eLpNorm (⇑Γ) (xbbQ1 d β) volume ≤ ENNReal.ofReal C * xbbN β ⇑Γ := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hden : 0 < (d : ℝ) - 2 * β := by linarith
  have hx : 0 < 2 * (d : ℝ) / (d - 2 * β) := by positivity
  have hlt : (2 : ℝ≥0∞) < xbbQ1 d β := by
    unfold xbbQ1
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ENNReal.ofReal_lt_ofReal_iff hx]
    rw [lt_div_iff₀ hden]; linarith
  have hrel : (xbbQ1 d β)⁻¹ = (2 : ℝ≥0∞)⁻¹ - ENNReal.ofReal (β / d) := by
    unfold xbbQ1
    rw [← ENNReal.ofReal_inv_of_pos hx, show (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp,
      ← ENNReal.ofReal_sub _ (by positivity)]
    congr 1
    field_simp
  obtain ⟨C, hC, h⟩ := cmxHLS_main hd β 2 (xbbQ1 d β) (by norm_num) hlt
    (by unfold xbbQ1; exact ENNReal.ofReal_lt_top) hβ hrel
  refine ⟨C, hC, fun Γ G hG => ?_⟩
  have hfrac : cmxHLS_frac β Γ = ⇑G := by
    funext x
    unfold cmxHLS_frac
    have e : (fun ξ : 𝔼 => (((2 * Real.pi * ‖ξ‖) ^ β : ℝ) : ℂ) * 𝓕 (⇑Γ) ξ) = 𝓕 (⇑G) := by
      funext ξ; rw [hG ξ]
    rw [e]
    have h1 : (𝓕⁻ (𝓕 G) : 𝓢(𝔼, ℂ)) = G := FourierTransform.fourierInv_fourier_eq G
    have h2 := congrFun (congrArg (⇑) h1) x
    rw [SchwartzMap.fourierInv_coe, SchwartzMap.fourier_coe] at h2
    exact h2
  refine (h Γ).trans ?_
  rw [hfrac, xbb_eLpNorm_two_eq]
  gcongr
  refine (xbbN_mono_fourier (β₁ := 0) (β₂ := β) (u := ⇑G) (v := ⇑Γ) (C := 1) zero_le_one
    (fun ξ => ?_)).trans (by simp)
  rw [Real.rpow_zero, one_mul, one_mul, hG ξ, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]


/-- exponent `d/β` -/
def xbbQ0 (d : ℕ) (β : ℝ) : ℝ≥0∞ := ENNReal.ofReal (d / β)

lemma xbbQ0_inv_add (hd : 1 ≤ d) {β : ℝ} (hβ : 0 < β) (hβd : 2 * β < d) :
    (xbbQ0 d β)⁻¹ + (xbbQ1 d β)⁻¹ = (2 : ℝ≥0∞)⁻¹ := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hden : 0 < (d : ℝ) - 2 * β := by linarith
  unfold xbbQ0 xbbQ1
  rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_inv_of_pos (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity), show (2 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 2) by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]; simp]
  congr 1
  field_simp
  ring

lemma one_lt_xbbQ0 (hd : 1 ≤ d) {β : ℝ} (hβ : 0 < β) (hβd : 2 * β < d) : 1 < xbbQ0 d β := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  unfold xbbQ0
  rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (by positivity), lt_div_iff₀ hβ]
  linarith

lemma one_lt_xbbQ1 (hd : 1 ≤ d) {β : ℝ} (hβ : 0 < β) (hβd : 2 * β < d) : 1 < xbbQ1 d β := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hden : 0 < (d : ℝ) - 2 * β := by linarith
  unfold xbbQ1
  rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (by positivity), lt_div_iff₀ hden]
  linarith

/-- **Kato–Ponce, low-frequency factor** (scale `1`): `f` Fourier-supported in `|ξ| ≤ 4`, `Γ`
Fourier-supported in `|ξ| ≥ 1`. -/
lemma xbb_pair_low (hd : 1 ≤ d) {β : ℝ} (hβ : 0 < β) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (f Γ : 𝓢(𝔼, ℂ)), (∀ ξ : 𝔼, 4 < ‖ξ‖ → 𝓕 (⇑f) ξ = 0) →
      (∀ ξ : 𝔼, ‖ξ‖ < 1 → 𝓕 (⇑Γ) ξ = 0) → ∀ B : ℝ, 0 ≤ B → (∀ x, ‖f x‖ ≤ B) →
        xbbN β (fun x => f x * Γ x) ≤ C * ENNReal.ofReal B * xbbN β ⇑Γ := by
  obtain ⟨CL, hCL, hL⟩ := main_uncond β hd hβ (r := 2) (p₁ := ⊤) (q₁ := 2) (p₂ := 2) (q₂ := ⊤)
    (by norm_num) (by norm_num) (by simp) (by norm_num) (by norm_num) (by simp) (by simp) (by simp)
  obtain ⟨Cb, hCb, hb⟩ := xbb_bernstein β
  refine ⟨CL * (Cb * ENNReal.ofReal ((2 * Real.pi) ^ (-β)) +
    ENNReal.ofReal ((1 + 1 / (4 * Real.pi ^ 2)) ^ (β / 2))), ?_, ?_⟩
  · exact ENNReal.mul_ne_top hCL (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hCb ENNReal.ofReal_ne_top,
      ENNReal.ofReal_ne_top⟩)
  intro f Γ hf hΓ B hB hfB
  have h1 := xbbN_le_Fm hβ.le (prodS f Γ)
  have h2 := hL f Γ
  have h3 := hb f hf B hB hfB
  have h4 := eLpNorm_two_le_xbbN hβ.le Γ hΓ
  have h5 := eLpNorm_Fm_le hβ.le Γ hΓ
  have h6 : eLpNorm (⇑f) ⊤ volume ≤ ENNReal.ofReal B := by
    rw [eLpNorm_exponent_top]
    · exact eLpNormEssSup_le_of_ae_bound (Eventually.of_forall hfB)
    · exact f.continuous.aestronglyMeasurable
  have e : (fun x => f x * Γ x) = ⇑(prodS f Γ) := rfl
  rw [e]
  calc xbbN β ⇑(prodS f Γ) ≤ eLpNorm (⇑(Fm β (prodS f Γ))) 2 volume := h1
    _ ≤ CL * (eLpNorm (⇑(Fm β f)) ⊤ volume * eLpNorm (⇑Γ) 2 volume +
          eLpNorm (⇑(Fm β Γ)) 2 volume * eLpNorm (⇑f) ⊤ volume) := h2
    _ ≤ CL * ((Cb * ENNReal.ofReal B) * (ENNReal.ofReal ((2 * Real.pi) ^ (-β)) * xbbN β ⇑Γ) +
          (ENNReal.ofReal ((1 + 1 / (4 * Real.pi ^ 2)) ^ (β / 2)) * xbbN β ⇑Γ) * ENNReal.ofReal B) := by
        gcongr
    _ = _ := by ring


/-- **Kato–Ponce, high-frequency factor** (scale `1`): `f` Fourier-supported in `|ξ| ≥ 2` with
companion `G` (`|∇|^β f`), `Γ` Fourier-supported in `|ξ| ≥ 1`. -/
lemma xbb_pair_high (hd : 3 ≤ d) {β : ℝ} (hβ : 0 < β) (hβd : 2 * β < d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (f G Γ : 𝓢(𝔼, ℂ)), XComp β f G →
      (∀ ξ : 𝔼, ‖ξ‖ < 2 → 𝓕 (⇑f) ξ = 0) → (∀ ξ : 𝔼, ‖ξ‖ < 1 → 𝓕 (⇑Γ) ξ = 0) →
      ∀ B : ℝ, 0 ≤ B → (∀ x, ‖f x‖ ≤ B) →
        xbbN β (fun x => f x * Γ x) ≤ C * (eLpNorm (⇑G) (xbbQ0 d β) volume *
          eLpNorm (⇑Γ) (xbbQ1 d β) volume + ENNReal.ofReal B * xbbN β ⇑Γ) := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (d : ℝ) > 0 := by exact_mod_cast hd1
  obtain ⟨CL, hCL, hL⟩ := main_uncond β hd1 hβ (r := 2) (p₁ := xbbQ0 d β) (q₁ := xbbQ1 d β)
    (p₂ := 2) (q₂ := ⊤) (by norm_num) (by norm_num) (one_lt_xbbQ0 hd1 hβ hβd)
    (one_lt_xbbQ1 hd1 hβ hβd) (by norm_num) (by simp) (xbbQ0_inv_add hd1 hβ hβd) (by simp)
  obtain ⟨Cbe, hCbe, hbe⟩ := xbb_bessel_hom hd hβ (by linarith : β < d)
  refine ⟨CL * (Cbe + ENNReal.ofReal ((1 + 1 / (4 * Real.pi ^ 2)) ^ (β / 2))), ?_, ?_⟩
  · exact ENNReal.mul_ne_top hCL (ENNReal.add_ne_top.2 ⟨hCbe, ENNReal.ofReal_ne_top⟩)
  intro f G Γ hG hf hΓ B hB hfB
  have h1 := xbbN_le_Fm hβ.le (prodS f Γ)
  have h2 := hL f Γ
  have h3 := hbe f G hG hf (xbbQ0 d β) (one_lt_xbbQ0 hd1 hβ hβd).le
  have h5 := eLpNorm_Fm_le hβ.le Γ hΓ
  have h6 : eLpNorm (⇑f) ⊤ volume ≤ ENNReal.ofReal B := by
    rw [eLpNorm_exponent_top]
    · exact eLpNormEssSup_le_of_ae_bound (Eventually.of_forall hfB)
    · exact f.continuous.aestronglyMeasurable
  have e : (fun x => f x * Γ x) = ⇑(prodS f Γ) := rfl
  rw [e]
  calc xbbN β ⇑(prodS f Γ) ≤ eLpNorm (⇑(Fm β (prodS f Γ))) 2 volume := h1
    _ ≤ CL * (eLpNorm (⇑(Fm β f)) (xbbQ0 d β) volume * eLpNorm (⇑Γ) (xbbQ1 d β) volume +
          eLpNorm (⇑(Fm β Γ)) 2 volume * eLpNorm (⇑f) ⊤ volume) := h2
    _ ≤ CL * ((Cbe * eLpNorm (⇑G) (xbbQ0 d β) volume) * eLpNorm (⇑Γ) (xbbQ1 d β) volume +
          (ENNReal.ofReal ((1 + 1 / (4 * Real.pi ^ 2)) ^ (β / 2)) * xbbN β ⇑Γ) * ENNReal.ofReal B) := by
        gcongr
    _ ≤ _ := by
        set X := eLpNorm (⇑G) (xbbQ0 d β) volume * eLpNorm (⇑Γ) (xbbQ1 d β) volume with hX
        set Y := ENNReal.ofReal B * xbbN β ⇑Γ with hY
        set c3 := ENNReal.ofReal ((1 + 1 / (4 * Real.pi ^ 2)) ^ (β / 2))
        have : (Cbe * eLpNorm (⇑G) (xbbQ0 d β) volume) * eLpNorm (⇑Γ) (xbbQ1 d β) volume +
            (c3 * xbbN β ⇑Γ) * ENNReal.ofReal B = Cbe * X + c3 * Y := by
          rw [hX, hY]; ring
        rw [this, mul_assoc]
        gcongr
        calc Cbe * X + c3 * Y ≤ (Cbe + c3) * X + (Cbe + c3) * Y := add_le_add (by gcongr; exact le_self_add) (by gcongr; exact le_add_self)
          _ = (Cbe + c3) * (X + Y) := by ring

end HRS.Commutator.Whole.XBB
