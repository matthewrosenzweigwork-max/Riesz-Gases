import HRS.Commutator.Whole.XBBAux1

/-!
# Packet XBB, part 2: dilations, the Sobolev seminorms `xbbN`, Fatou and the triangle inequality
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section
namespace HRS.Commutator.Whole.XBB
open HRS.Commutator.Whole HRS.Commutator.Whole.XLI HRS.Commutator.Whole.XNRS
variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- dilation of a Schwartz function: `(xbbDil c h)(x) = h(c x)` -/
def xbbDil (c : ℝ) (hc : c ≠ 0) (h : 𝓢(𝔼, ℂ)) : 𝓢(𝔼, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (Units.mk0 c hc)) h

lemma xbbDil_apply (c : ℝ) (hc : c ≠ 0) (h : 𝓢(𝔼, ℂ)) (x : 𝔼) : xbbDil c hc h x = h (c • x) := rfl

lemma xbb_fourier_dil {c : ℝ} (hc : 0 < c) (h : 𝓢(𝔼, ℂ)) (ξ : 𝔼) :
    𝓕 (⇑(xbbDil c hc.ne' h)) ξ = ((c ^ d)⁻¹ : ℝ) • 𝓕 (⇑h) (c⁻¹ • ξ) := by
  have : (⇑(xbbDil c hc.ne' h) : 𝔼 → ℂ) = fun x => h (c • x) := rfl
  rw [this]
  exact fourier_comp_smul' (⇑h) hc ξ

lemma xbb_lintegral_comp_smul (G : 𝔼 → ℝ≥0∞) (hG : Measurable G) {c : ℝ} (hc : 0 < c) :
    ∫⁻ x, G (c • x) = ENNReal.ofReal ((c ^ d)⁻¹) * ∫⁻ x, G x := by
  have hm : Measurable (fun x : 𝔼 => c • x) := measurable_const_smul c
  have h1 := lintegral_map hG hm (μ := (volume : Measure 𝔼))
  rw [Measure.map_addHaar_smul (volume : Measure 𝔼) hc.ne', lintegral_smul_measure] at h1
  rw [← h1]
  simp [finrank_euclideanSpace, abs_of_pos, hc]


lemma xbb_eLpNorm_dil {c : ℝ} (hc : 0 < c) (h : 𝓢(𝔼, ℂ)) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ⊤) :
    eLpNorm (⇑(xbbDil c hc.ne' h)) p volume
      = ENNReal.ofReal (c ^ (-(d : ℝ) / p.toReal)) * eLpNorm (⇑h) p volume := by
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt]
  have hG : Measurable (fun x : 𝔼 => ‖h x‖ₑ ^ p.toReal) :=
    (h.continuous.measurable.enorm).pow_const _
  have h1 : ∫⁻ x, ‖xbbDil c hc.ne' h x‖ₑ ^ p.toReal = ENNReal.ofReal ((c ^ d)⁻¹) * ∫⁻ x, ‖h x‖ₑ ^ p.toReal := by
    have := xbb_lintegral_comp_smul (fun x => ‖h x‖ₑ ^ p.toReal) hG hc
    simpa [xbbDil_apply] using this
  rw [h1, ENNReal.mul_rpow_of_nonneg _ _ (div_nonneg zero_le_one hpr.le)]
  congr 1
  have key : ((c ^ d)⁻¹) ^ (1 / p.toReal) = c ^ (-(d : ℝ) / p.toReal) := by
    rw [← Real.rpow_natCast c d, ← Real.rpow_neg hc.le, ← Real.rpow_mul hc.le]
    congr 1; ring
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (div_nonneg zero_le_one hpr.le), key]
  all_goals first | exact h.continuous.aestronglyMeasurable | exact (xbbDil c hc.ne' h).continuous.aestronglyMeasurable


/-- the homogeneous Sobolev seminorm squared, `∫ (2π|ξ|)^{2β} |𝓕u|²`, as an extended real -/
def xbbQ (β : ℝ) (u : 𝔼 → ℂ) : ℝ≥0∞ :=
  ∫⁻ ξ, (ENNReal.ofReal ((2 * Real.pi * ‖ξ‖) ^ β) * ‖𝓕 u ξ‖ₑ) ^ (2 : ℝ)

/-- the homogeneous Sobolev seminorm -/
def xbbN (β : ℝ) (u : 𝔼 → ℂ) : ℝ≥0∞ := xbbQ β u ^ (1 / 2 : ℝ)

lemma xbb_fourier_add {u v : 𝔼 → ℂ} (hu : Integrable u) (hv : Integrable v) (ξ : 𝔼) :
    𝓕 (fun x => u x + v x) ξ = 𝓕 u ξ + 𝓕 v ξ := by
  have h := VectorFourier.fourierIntegral_add (e := Real.fourierChar) (μ := (volume : Measure 𝔼))
    (L := innerₗ 𝔼) Real.continuous_fourierChar (by exact continuous_inner) hu hv
  have h2 := congrFun h ξ
  simpa [Real.fourier_eq, VectorFourier.fourierIntegral] using h2

lemma continuous_fourier_of_integrable {u : 𝔼 → ℂ} (hu : Integrable u) : Continuous (𝓕 u) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by exact continuous_inner) hu

lemma xbbQ_measurable_integrand (β : ℝ) {u : 𝔼 → ℂ} (hu : Integrable u) :
    Measurable (fun ξ : 𝔼 => (ENNReal.ofReal ((2 * Real.pi * ‖ξ‖) ^ β) * ‖𝓕 u ξ‖ₑ) ^ (2 : ℝ)) := by
  have h1 : Measurable (fun ξ : 𝔼 => ENNReal.ofReal ((2 * Real.pi * ‖ξ‖) ^ β)) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  exact (h1.mul (continuous_fourier_of_integrable hu).measurable.enorm).pow_const _

lemma xbbN_add_le (β : ℝ) {u v : 𝔼 → ℂ} (hu : Integrable u) (hv : Integrable v) :
    xbbN β (fun x => u x + v x) ≤ xbbN β u + xbbN β v := by
  unfold xbbN xbbQ
  have h1 : Measurable (fun ξ : 𝔼 => ENNReal.ofReal ((2 * Real.pi * ‖ξ‖) ^ β)) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have hfu : AEMeasurable (fun ξ : 𝔼 => ENNReal.ofReal ((2 * Real.pi * ‖ξ‖) ^ β) * ‖𝓕 u ξ‖ₑ) volume :=
    (h1.mul (continuous_fourier_of_integrable hu).measurable.enorm).aemeasurable
  have hfv : AEMeasurable (fun ξ : 𝔼 => ENNReal.ofReal ((2 * Real.pi * ‖ξ‖) ^ β) * ‖𝓕 v ξ‖ₑ) volume :=
    (h1.mul (continuous_fourier_of_integrable hv).measurable.enorm).aemeasurable
  have := ENNReal.lintegral_Lp_add_le hfu hfv (by norm_num : (1 : ℝ) ≤ 2)
  refine le_trans ?_ this
  refine ENNReal.rpow_le_rpow (lintegral_mono fun ξ => ?_) (by norm_num)
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  simp only [Pi.add_apply]
  rw [xbb_fourier_add hu hv, ← mul_add]
  gcongr
  exact enorm_add_le _ _

lemma xbbQ_fatou (β : ℝ) {u : ℕ → 𝔼 → ℂ} {v : 𝔼 → ℂ} (hu : ∀ k, Integrable (u k))
    (hlim : ∀ ξ : 𝔼, Tendsto (fun k => 𝓕 (u k) ξ) atTop (𝓝 (𝓕 v ξ))) {M : ℝ≥0∞}
    (hM : ∃ᶠ k in atTop, xbbQ β (u k) ≤ M) : xbbQ β v ≤ M := by
  set g : ℕ → 𝔼 → ℝ≥0∞ := fun k ξ => (ENNReal.ofReal ((2 * Real.pi * ‖ξ‖) ^ β) * ‖𝓕 (u k) ξ‖ₑ) ^ (2 : ℝ)
    with hg
  have hgm : ∀ k, Measurable (g k) := fun k => xbbQ_measurable_integrand β (hu k)
  have hpt : ∀ ξ : 𝔼, (ENNReal.ofReal ((2 * Real.pi * ‖ξ‖) ^ β) * ‖𝓕 v ξ‖ₑ) ^ (2 : ℝ) =
      liminf (fun k => g k ξ) atTop := by
    intro ξ
    have h1 : Tendsto (fun k => ‖𝓕 (u k) ξ‖ₑ) atTop (𝓝 ‖𝓕 v ξ‖ₑ) :=
      (continuous_enorm.tendsto _).comp (hlim ξ)
    have h2 : Tendsto (fun k => ENNReal.ofReal ((2 * Real.pi * ‖ξ‖) ^ β) * ‖𝓕 (u k) ξ‖ₑ) atTop
        (𝓝 (ENNReal.ofReal ((2 * Real.pi * ‖ξ‖) ^ β) * ‖𝓕 v ξ‖ₑ)) :=
      ENNReal.Tendsto.const_mul h1 (Or.inr ENNReal.ofReal_ne_top)
    have h3 : Tendsto (fun k => g k ξ) atTop
        (𝓝 ((ENNReal.ofReal ((2 * Real.pi * ‖ξ‖) ^ β) * ‖𝓕 v ξ‖ₑ) ^ (2 : ℝ))) :=
      (ENNReal.continuous_rpow_const.tendsto _).comp h2
    exact h3.liminf_eq.symm
  unfold xbbQ
  calc ∫⁻ ξ, (ENNReal.ofReal ((2 * Real.pi * ‖ξ‖) ^ β) * ‖𝓕 v ξ‖ₑ) ^ (2 : ℝ)
      = ∫⁻ ξ, liminf (fun k => g k ξ) atTop := lintegral_congr hpt
    _ ≤ liminf (fun k => ∫⁻ ξ, g k ξ) atTop := lintegral_liminf_le hgm
    _ ≤ M := liminf_le_of_frequently_le' hM


/-- monotonicity of the Sobolev seminorms in the Fourier modulus -/
lemma xbbN_mono_fourier {β₁ β₂ : ℝ} {u v : 𝔼 → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ξ : 𝔼, (2 * Real.pi * ‖ξ‖) ^ β₁ * ‖𝓕 u ξ‖ ≤ C * ((2 * Real.pi * ‖ξ‖) ^ β₂ * ‖𝓕 v ξ‖)) :
    xbbN β₁ u ≤ ENNReal.ofReal C * xbbN β₂ v := by
  unfold xbbN xbbQ
  have h1 : ∀ ξ : 𝔼, ENNReal.ofReal ((2 * Real.pi * ‖ξ‖) ^ β₁) * ‖𝓕 u ξ‖ₑ ≤
      ENNReal.ofReal C * (ENNReal.ofReal ((2 * Real.pi * ‖ξ‖) ^ β₂) * ‖𝓕 v ξ‖ₑ) := by
    intro ξ
    have h0 : 0 ≤ (2 * Real.pi * ‖ξ‖) ^ β₁ := by positivity
    have h0' : 0 ≤ (2 * Real.pi * ‖ξ‖) ^ β₂ := by positivity
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul h0, ← ENNReal.ofReal_mul h0',
      ← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal (h ξ)
  calc (∫⁻ ξ, (ENNReal.ofReal ((2 * Real.pi * ‖ξ‖) ^ β₁) * ‖𝓕 u ξ‖ₑ) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ ξ, (ENNReal.ofReal C * (ENNReal.ofReal ((2 * Real.pi * ‖ξ‖) ^ β₂) * ‖𝓕 v ξ‖ₑ)) ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (lintegral_mono fun ξ => ENNReal.rpow_le_rpow (h1 ξ) (by norm_num))
          (by norm_num)
    _ = ENNReal.ofReal C * (∫⁻ ξ, (ENNReal.ofReal ((2 * Real.pi * ‖ξ‖) ^ β₂) * ‖𝓕 v ξ‖ₑ) ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top),
          ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), ← ENNReal.rpow_mul]
        norm_num

/-- Plancherel for Schwartz functions -/
lemma xbb_eLpNorm_two_eq (h : 𝓢(𝔼, ℂ)) : eLpNorm (⇑h) 2 volume = xbbN 0 ⇑h := by
  have hp := plancherel_L1L2 h.integrable (h.memLp 2)
  unfold xbbN xbbQ
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  · simp only [ENNReal.toReal_ofNat, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
    congr 1
    have : ∀ x : ℝ≥0∞, x ^ (2 : ℝ) = x ^ 2 := fun x => ENNReal.rpow_two x
    simp_rw [this]
    exact hp.symm
  · exact h.continuous.aestronglyMeasurable


lemma xbbQ_dil (β : ℝ) {c : ℝ} (hc : 0 < c) (u : 𝓢(𝔼, ℂ)) :
    xbbQ β ⇑(xbbDil c hc.ne' u) = ENNReal.ofReal (c ^ (2 * β - d)) * xbbQ β ⇑u := by
  unfold xbbQ
  set G : 𝔼 → ℝ≥0∞ := fun ζ => (ENNReal.ofReal ((2 * Real.pi * ‖ζ‖) ^ β) * ‖𝓕 (⇑u) ζ‖ₑ) ^ (2 : ℝ)
    with hG
  have hGm : Measurable G := xbbQ_measurable_integrand β u.integrable
  have hpt : ∀ ξ : 𝔼, (ENNReal.ofReal ((2 * Real.pi * ‖ξ‖) ^ β) *
      ‖𝓕 (⇑(xbbDil c hc.ne' u)) ξ‖ₑ) ^ (2 : ℝ) =
      ENNReal.ofReal (c ^ (2 * β) * ((c ^ d)⁻¹) ^ 2) * G (c⁻¹ • ξ) := by
    intro ξ
    have hn : ‖ξ‖ = c * ‖c⁻¹ • ξ‖ := by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hc.le]; field_simp
    rw [xbb_fourier_dil hc, hG]
    simp only
    rw [enorm_smul, hn]
    set a : ℝ := (2 * Real.pi * ‖c⁻¹ • ξ‖) ^ β with ha
    have ha0 : 0 ≤ a := by positivity
    have e1 : (2 * Real.pi * (c * ‖c⁻¹ • ξ‖)) ^ β = c ^ β * a := by
      rw [ha, ← Real.mul_rpow hc.le (by positivity)]; congr 1; ring
    rw [e1]
    have e2 : ‖((c ^ d)⁻¹ : ℝ)‖ₑ = ENNReal.ofReal ((c ^ d)⁻¹) := by
      rw [← ofReal_norm, Real.norm_of_nonneg (by positivity)]
    rw [e2, ENNReal.ofReal_mul (by positivity)]
    have e3 : ENNReal.ofReal (c ^ (2 * β) * ((c ^ d)⁻¹) ^ 2) =
        (ENNReal.ofReal (c ^ β) * ENNReal.ofReal ((c ^ d)⁻¹)) ^ (2 : ℝ) := by
      rw [← ENNReal.ofReal_mul (by positivity), ENNReal.rpow_two, ← ENNReal.ofReal_pow (by positivity)]
      congr 1
      have : c ^ (2 * β) = (c ^ β) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]; congr 1; push_cast; ring
      rw [this]; ring
    rw [e3, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have := xbb_lintegral_comp_smul G hGm (inv_pos.2 hc)
  rw [this, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  rw [inv_pow c d, inv_inv, Real.rpow_sub hc, Real.rpow_natCast]
  field_simp


lemma xbbN_dil (β : ℝ) {c : ℝ} (hc : 0 < c) (u : 𝓢(𝔼, ℂ)) :
    xbbN β ⇑(xbbDil c hc.ne' u) = ENNReal.ofReal (c ^ (β - (d : ℝ) / 2)) * xbbN β ⇑u := by
  unfold xbbN
  rw [xbbQ_dil β hc u, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.rpow_mul hc.le]
  congr 3
  ring

lemma xbbQ_eq_ofReal_xhom {β : ℝ} (hβ : 0 ≤ β) (g : 𝓢(𝔼, ℂ)) :
    xbbQ β ⇑g = ENNReal.ofReal (xhom β g) := by
  unfold xbbQ xhom
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_xhom hβ g)
    (Eventually.of_forall fun ξ => by positivity)]
  refine lintegral_congr fun ξ => ?_
  have h0 : 0 ≤ (2 * Real.pi * ‖ξ‖) ^ β := by positivity
  rw [← ofReal_norm, ← ENNReal.ofReal_mul h0, ENNReal.rpow_two,
    ← ENNReal.ofReal_pow (by positivity)]
  congr 1
  rw [SchwartzMap.fourier_coe, mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 2
  push_cast; ring

end HRS.Commutator.Whole.XBB
