import HRS.MS.ThCorrSobAux1
import HRS.MS.PsdHeatAux1

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ComplexConjugate FourierTransform Convolution ContDiff

namespace HRS.MS.Tc3
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.Whole HRS.Whole.Q34 HRS.MS.SobMul HRS.MS.Psd

variable {d : ℕ}

theorem tc3_integral_circle_smul {α : Type*} [MeasurableSpace α] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {μ : Measure α} (c : Circle) (f : α → E) :
    ∫ x, c • f x ∂μ = c • ∫ x, f x ∂μ := by
  have : ∀ y : E, c • y = (c : ℂ) • y := fun y => rfl
  simp only [this]
  exact integral_smul _ _

/-- Product formula: `\widehat{T h}(ξ) = ∫ T̂(η) ĥ(ξ - η) dη` for Schwartz `T` and `h ∈ L¹`. -/
theorem tc3_fourier_mul (T : SchwartzMap (Euc d) ℂ) {h : Euc d → ℂ} (hh : Integrable h volume)
    (ξ : Euc d) :
    𝓕 (fun x => T x * h x) ξ =
      ∫ η, (𝓕 T : SchwartzMap (Euc d) ℂ) η * 𝓕 h (ξ - η) := by
  set a : SchwartzMap (Euc d) ℂ := 𝓕 T with ha
  have hT : ∀ x, T x = ∫ η, 𝐞 (inner ℝ η x) • a η := by
    intro x
    have h0 : 𝓕⁻ a = T := by simp [ha]
    have := congrArg (fun F : SchwartzMap (Euc d) ℂ => F x) h0
    try simp only at this
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq] at this
    exact this.symm
  have hai : Integrable (fun η => a η) volume := a.integrable
  have key : ∀ x η : Euc d, 𝐞 (-inner ℝ x ξ) • ((𝐞 (inner ℝ η x) • a η) * h x) =
      a η * (𝐞 (-inner ℝ x (ξ - η)) • h x) := by
    intro x η
    have e : (-inner ℝ x (ξ - η) : ℝ) = -inner ℝ x ξ + inner ℝ η x := by
      rw [inner_sub_right, real_inner_comm x η]; ring
    rw [e, AddChar.map_add_eq_mul]
    simp only [Circle.smul_def, smul_eq_mul, Circle.coe_mul]; ring
  have hF : Integrable (Function.uncurry fun (x η : Euc d) =>
      𝐞 (-inner ℝ x ξ) • ((𝐞 (inner ℝ η x) • a η) * h x)) (volume.prod volume) := by
    have h1 : Integrable (fun p : Euc d × Euc d => ‖h p.1‖ * ‖a p.2‖) (volume.prod volume) :=
      hh.norm.mul_prod hai.norm
    refine h1.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · have c1 : Continuous fun p : Euc d × Euc d => (𝐞 (-inner ℝ p.1 ξ) : Circle) :=
        Real.continuous_fourierChar.comp (by fun_prop)
      have c2 : Continuous fun p : Euc d × Euc d => (𝐞 (inner ℝ p.2 p.1) : Circle) :=
        Real.continuous_fourierChar.comp (by fun_prop)
      refine c1.aestronglyMeasurable.smul ?_
      refine AEStronglyMeasurable.mul ?_ (hh.1.comp_fst)
      exact c2.aestronglyMeasurable.smul (a.continuous.comp continuous_snd).aestronglyMeasurable
    · show ‖𝐞 (-inner ℝ p.1 ξ) • ((𝐞 (inner ℝ p.2 p.1) • a p.2) * h p.1)‖ ≤ ‖h p.1‖ * ‖a p.2‖
      simp only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul]
      rw [mul_comm]
  rw [Real.fourier_eq]
  have e1 : ∀ x, 𝐞 (-inner ℝ x ξ) • (T x * h x) =
      ∫ η, 𝐞 (-inner ℝ x ξ) • ((𝐞 (inner ℝ η x) • a η) * h x) := by
    intro x
    rw [tc3_integral_circle_smul, integral_mul_const, ← hT x]
  simp_rw [e1]
  rw [integral_integral_swap hF]
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  simp only [key]
  rw [integral_const_mul, Real.fourier_eq]

theorem tc3_heat_ft {t : ℝ} (ht : 0 < t) (w : Euc d) :
    𝓕 (fun v : Euc d => ((heatKerE d t v : ℝ) : ℂ)) w =
      ((Real.exp (-(4 * Real.pi ^ 2 * t * ‖w‖ ^ 2)) : ℝ) : ℂ) := by
  set b : ℂ := ((1 / (4 * t) : ℝ) : ℂ) with hb
  have hbre : 0 < b.re := by
    rw [hb, Complex.ofReal_re]; positivity
  set c : ℝ := (4 * Real.pi * t) ^ (-(d : ℝ) / 2) with hc
  have h1 : (fun v : Euc d => ((heatKerE d t v : ℝ) : ℂ)) =
      (c : ℂ) • (fun v : Euc d => Complex.exp (-b * (‖v‖ : ℂ) ^ 2)) := by
    funext v
    simp only [heatKerE, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
    congr 1
    rw [Complex.ofReal_exp]
    congr 1
    rw [hb]
    push_cast
    field_simp
  have hsm : ∀ (c : ℂ) (f : Euc d → ℂ) (w : Euc d), 𝓕 (c • f) w = c * 𝓕 f w := by
    intro c f w
    simp only [Real.fourier_eq, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext v
    simp only [Circle.smul_def, smul_eq_mul]
    ring
  rw [h1, hsm, fourier_gaussian_innerProductSpace hbre]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul]
  have e1 : (Real.pi : ℂ) / b = ((4 * Real.pi * t : ℝ) : ℂ) := by
    rw [hb]; push_cast; field_simp
  have e2 : (-(Real.pi : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2 / b) =
      ((-(4 * Real.pi ^ 2 * t * ‖w‖ ^ 2) : ℝ) : ℂ) := by
    rw [hb]; push_cast; field_simp
  rw [e1, e2, ← Complex.ofReal_exp]
  have e3 : (((4 * Real.pi * t : ℝ) : ℂ)) ^ ((d : ℂ) / 2) = (((4 * Real.pi * t) ^ ((d : ℝ) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast; rfl
  rw [e3, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  have e4 : c * (4 * Real.pi * t) ^ ((d : ℝ) / 2) = 1 := by
    rw [hc, ← Real.rpow_add (by positivity)]
    have : -(d : ℝ) / 2 + (d : ℝ) / 2 = 0 := by ring
    rw [this, Real.rpow_zero]
  rw [← mul_assoc, e4, one_mul]

/-- the local kernel `θ g` -/
def tc3_Gloc (d : ℕ) (s : ℝ) (θ : Euc d → ℝ) (x : Euc d) : ℝ := θ x * rieszKernel d s x

theorem tc3_measurable_riesz (s : ℝ) : Measurable (rieszKernel d s) := by
  by_cases hs : s = 0
  · have : rieszKernel d s = fun z : Euc d => -Real.log ‖z‖ := by
      funext z; simp [rieszKernel, hs]
    rw [this]; exact (Real.measurable_log.comp measurable_norm).neg
  · exact measurable_rieszKernel hs

theorem tc3_Gloc_measurable {θ : Euc d → ℝ} (hθ : Continuous θ) (s : ℝ) :
    Measurable (tc3_Gloc d s θ) :=
  hθ.measurable.mul (tc3_measurable_riesz s)

theorem tc3_Gloc_integrable {θ : Euc d → ℝ} (hθ : Continuous θ) (hc : HasCompactSupport θ)
    {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) : Integrable (tc3_Gloc d s θ) volume := by
  have := (rieszKernel_locallyIntegrable hs0 hsd).integrable_smul_left_of_hasCompactSupport hθ hc
  exact this

theorem tc3_riesz_rep {s : ℝ} (hs : 0 < s) (x : Euc d) :
    ‖x‖ ^ (-s) = ∫ t in Ioi (0 : ℝ), psd3_F d s t x := by
  have hG : 0 < Real.Gamma (s / 2) := Real.Gamma_pos_of_pos (by linarith)
  obtain ⟨_, hv⟩ := psd3_cov hs x
  rw [hv]
  unfold psd3_psi
  rw [integral_const_mul]
  have := riesz_heat hs x
  rw [← this]
  field_simp

theorem tc3_psdF_integrableOn {s : ℝ} (hs : 0 < s) {x : Euc d} (hx : x ≠ 0) :
    IntegrableOn (fun t : ℝ => psd3_F d s t x) (Ioi (0 : ℝ)) := by
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hψ : IntegrableOn (psd3_psi d s x) (Ioi (0 : ℝ)) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s / 2 - 1) (b := ‖x‖ ^ 2)
      (by linarith) one_pos (by positivity)
    have h2 : IntegrableOn (fun l : ℝ => (Real.Gamma (s / 2))⁻¹ *
        (l ^ (s / 2 - 1) * Real.exp (-(‖x‖ ^ 2 * l)))) (Ioi (0 : ℝ)) := by
      refine Integrable.const_mul ?_ _
      refine this.congr_fun (fun l hl => ?_) measurableSet_Ioi
      simp only [Real.rpow_one]
      rw [neg_mul]
    exact h2
  exact ((psd3_cov hs x).1).2 hψ

/-- the integrand of the heat-kernel Fubini, for a weight `cw` -/
def tc3_Psi (θ : Euc d → ℝ) (cw : ℝ → ℝ) (ξ : Euc d) (x : Euc d) (t : ℝ) : ℂ :=
  𝐞 (-inner ℝ x ξ) • (((θ x : ℝ) : ℂ) * ((cw t * heatKerE d t x : ℝ) : ℂ))

theorem tc3_heat_meas : Measurable (fun p : ℝ × Euc d => heatKerE d p.1 p.2) := by
  unfold heatKerE
  have h1 : Measurable (fun p : ℝ × Euc d => p.1) := measurable_fst
  have h2 : Measurable (fun p : ℝ × Euc d => ‖p.2‖) := measurable_norm.comp measurable_snd
  refine ((measurable_const.mul h1).pow_const _).mul ?_
  exact Real.measurable_exp.comp (((h2.pow_const 2).neg).div (measurable_const.mul h1))

theorem tc3_Psi_norm (θ : Euc d → ℝ) {cw : ℝ → ℝ} (ξ x : Euc d) {t : ℝ} (ht : 0 ≤ t)
    (hcw : 0 ≤ cw t) : ‖tc3_Psi θ cw ξ x t‖ = |θ x| * (cw t * heatKerE d t x) := by
  unfold tc3_Psi
  simp only [Circle.smul_def, smul_eq_mul, norm_mul, Circle.norm_coe, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  rw [abs_of_nonneg hcw, abs_of_nonneg (psd3_heat_nonneg ht x)]

/-- Fubini: if `K(x) = ∫_0^∞ cw(t) p_t(x) dt` (a.e.), then `\widehat{θ K}(ξ) = ∫_0^∞ ∫ ...`. -/
theorem tc3_fubini {θ : Euc d → ℝ} (hθ : Continuous θ) {cw : ℝ → ℝ} (hcwm : Measurable cw)
    (hcw0 : ∀ t, 0 < t → 0 ≤ cw t) {K : Euc d → ℝ}
    (hrep : ∀ᵐ x ∂(volume : Measure (Euc d)), K x = ∫ t in Ioi (0 : ℝ), cw t * heatKerE d t x)
    (hae : ∀ᵐ x ∂(volume : Measure (Euc d)),
      IntegrableOn (fun t : ℝ => cw t * heatKerE d t x) (Ioi (0 : ℝ)))
    (hG : Integrable (fun x => θ x * K x) volume) (ξ : Euc d) :
    tc3_Ghat (fun x => θ x * K x) ξ = ∫ t in Ioi (0 : ℝ), ∫ x, tc3_Psi θ cw ξ x t := by
  have e : ∀ᵐ x ∂(volume : Measure (Euc d)), 𝐞 (-inner ℝ x ξ) • ((θ x * K x : ℝ) : ℂ) =
      ∫ t in Ioi (0 : ℝ), tc3_Psi θ cw ξ x t := by
    filter_upwards [hrep] with x hx
    unfold tc3_Psi
    rw [hx, tc3_integral_circle_smul, integral_const_mul, integral_complex_ofReal,
      Complex.ofReal_mul]
  have hmeas : AEStronglyMeasurable (Function.uncurry (tc3_Psi θ cw ξ))
      ((volume : Measure (Euc d)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hm1 : Measurable fun p : Euc d × ℝ => (𝐞 (-inner ℝ p.1 ξ) : Circle) :=
      (Real.continuous_fourierChar.comp (by fun_prop)).measurable
    have hm2 : Measurable fun p : Euc d × ℝ => ((θ p.1 : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp (hθ.measurable.comp measurable_fst)
    have hm3 : Measurable fun p : Euc d × ℝ => ((cw p.2 * heatKerE d p.2 p.1 : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp ((hcwm.comp measurable_snd).mul
        ((tc3_heat_meas (d := d)).comp measurable_swap))
    exact (hm1.smul (hm2.mul hm3)).aestronglyMeasurable
  have h1 : ∀ᵐ x ∂(volume : Measure (Euc d)),
      Integrable (fun t => tc3_Psi θ cw ξ x t) (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards [hae] with x hx
    refine Integrable.mono' (hx.const_mul |θ x|) ?_ ?_
    · have hm1 : Measurable fun t : ℝ => (𝐞 (-inner ℝ x ξ) : Circle) := measurable_const
      exact (hm1.smul (measurable_const.mul (Complex.measurable_ofReal.comp
        ((hcwm.mul ((tc3_heat_meas (d := d)).comp
          (measurable_id.prodMk measurable_const))))))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [tc3_Psi_norm θ ξ x (le_of_lt ht) (hcw0 t ht)]
  have h2 : Integrable (fun x => ∫ t in Ioi (0 : ℝ), ‖tc3_Psi θ cw ξ x t‖) volume := by
    refine hG.norm.congr ?_
    filter_upwards [hrep] with x hx
    show ‖θ x * K x‖ = ∫ t in Ioi (0 : ℝ), ‖tc3_Psi θ cw ξ x t‖
    have : ∫ t in Ioi (0 : ℝ), ‖tc3_Psi θ cw ξ x t‖ =
        |θ x| * ∫ t in Ioi (0 : ℝ), cw t * heatKerE d t x := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi fun t ht =>
        tc3_Psi_norm θ ξ x (le_of_lt ht) (hcw0 t ht)
    have hK0 : 0 ≤ K x := by
      rw [hx]
      exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
        mul_nonneg (hcw0 t ht) (psd3_heat_nonneg (le_of_lt ht) x)
    rw [this, ← hx, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg hK0]
  have hint := (integrable_prod_iff hmeas).2 ⟨h1, h2⟩
  unfold tc3_Ghat
  rw [Real.fourier_eq, integral_congr_ae e]
  exact integral_integral_swap hint

theorem tc3_Ht_enorm_le {θ : Euc d → ℝ} (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    {cw : ℝ → ℝ} (ξ : Euc d) {t : ℝ} (ht : 0 < t) (hcw : 0 ≤ cw t) :
    ‖∫ x, tc3_Psi θ cw ξ x t‖ₑ ≤ ∫⁻ η : Euc d,
      ENNReal.ofReal (cw t) *
        (‖(𝓕 (sobmul_T θ hθ hc) : SchwartzMap (Euc d) ℂ) η‖ₑ *
          ENNReal.ofReal (Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ - η‖ ^ 2)))) := by
  set T := sobmul_T θ hθ hc with hTdef
  set a : SchwartzMap (Euc d) ℂ := 𝓕 T with ha
  have hh : Integrable (fun x : Euc d => ((heatKerE d t x : ℝ) : ℂ)) volume :=
    (psd3_heat_integral ht).1.ofReal
  have e1 : ∫ x, tc3_Psi θ cw ξ x t =
      (cw t : ℂ) * 𝓕 (fun x => T x * ((heatKerE d t x : ℝ) : ℂ)) ξ := by
    rw [Real.fourier_eq, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    unfold tc3_Psi
    simp only [Circle.smul_def, smul_eq_mul, sobmul_T_apply, hTdef]
    push_cast
    ring
  rw [e1, tc3_fourier_mul T hh ξ, enorm_mul]
  have e2 : ∀ η : Euc d, a η * 𝓕 (fun x : Euc d => ((heatKerE d t x : ℝ) : ℂ)) (ξ - η) =
      a η * ((Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ - η‖ ^ 2)) : ℝ) : ℂ) := fun η => by
    rw [tc3_heat_ft ht]
  have e2' : (∫ η, a η * 𝓕 (fun x : Euc d => ((heatKerE d t x : ℝ) : ℂ)) (ξ - η)) =
      ∫ η, a η * ((Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ - η‖ ^ 2)) : ℝ) : ℂ) :=
    integral_congr_ae (Filter.Eventually.of_forall fun η => e2 η)
  rw [e2']
  have e3 : ‖(cw t : ℂ)‖ₑ = ENNReal.ofReal (cw t) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hcw]
  rw [e3, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  gcongr
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun η => ?_))
  rw [enorm_mul, ← ofReal_norm (((Real.exp _ : ℝ)) : ℂ), Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]

/-- generic `ℝ^d` bound: `‖\widehat{θK}(ξ)‖ₑ ≤ ∫⁻ η ‖T̂(η)‖ₑ ∫⁻_t cw(t) e^{-4π² t |ξ-η|²}`. -/
theorem tc3_Ghat_enorm_gen {θ : Euc d → ℝ} (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    {cw : ℝ → ℝ} (hcwm : Measurable cw) (hcw0 : ∀ t, 0 < t → 0 ≤ cw t) {K : Euc d → ℝ}
    (hrep : ∀ᵐ x ∂(volume : Measure (Euc d)), K x = ∫ t in Ioi (0 : ℝ), cw t * heatKerE d t x)
    (hae : ∀ᵐ x ∂(volume : Measure (Euc d)),
      IntegrableOn (fun t : ℝ => cw t * heatKerE d t x) (Ioi (0 : ℝ)))
    (hG : Integrable (fun x => θ x * K x) volume) (ξ : Euc d) :
    ‖tc3_Ghat (fun x => θ x * K x) ξ‖ₑ ≤ ∫⁻ η : Euc d,
      ‖(𝓕 (sobmul_T θ hθ hc) : SchwartzMap (Euc d) ℂ) η‖ₑ *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (cw t) *
          ENNReal.ofReal (Real.exp (-((4 * Real.pi ^ 2 * ‖ξ - η‖ ^ 2) * t))) := by
  set a : SchwartzMap (Euc d) ℂ := 𝓕 (sobmul_T θ hθ hc) with ha
  rw [tc3_fubini hθ.continuous hcwm hcw0 hrep hae hG ξ]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have hmeas : AEMeasurable (Function.uncurry fun (t : ℝ) (η : Euc d) =>
      ENNReal.ofReal (cw t) *
        (‖a η‖ₑ * ENNReal.ofReal (Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ - η‖ ^ 2)))))
      ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))|>.prod (volume : Measure (Euc d))) := by
    refine Measurable.aemeasurable ?_
    have h1 : Measurable fun p : ℝ × Euc d => p.1 := measurable_fst
    have h2 : Measurable fun p : ℝ × Euc d => ‖ξ - p.2‖ :=
      measurable_norm.comp (measurable_const.sub measurable_snd)
    refine (ENNReal.measurable_ofReal.comp (hcwm.comp measurable_fst)).mul ?_
    refine (a.continuous.measurable.enorm.comp measurable_snd).mul ?_
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((measurable_const.mul h1).mul (h2.pow_const 2)).neg))
  calc ∫⁻ t in Ioi (0 : ℝ), ‖∫ x, tc3_Psi θ cw ξ x t‖ₑ
      ≤ ∫⁻ t in Ioi (0 : ℝ), ∫⁻ η : Euc d,
          ENNReal.ofReal (cw t) *
            (‖a η‖ₑ * ENNReal.ofReal (Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ - η‖ ^ 2)))) := by
        refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        exact tc3_Ht_enorm_le hθ hc ξ ht (hcw0 t ht)
    _ = ∫⁻ η : Euc d, ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (cw t) *
            (‖a η‖ₑ * ENNReal.ofReal (Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ - η‖ ^ 2)))) :=
        lintegral_lintegral_swap hmeas
    _ = _ := by
        refine lintegral_congr fun η => ?_
        have e1 : ∀ t : ℝ, ENNReal.ofReal (cw t) *
            (‖a η‖ₑ * ENNReal.ofReal (Real.exp (-(4 * Real.pi ^ 2 * t * ‖ξ - η‖ ^ 2)))) =
            ‖a η‖ₑ * (ENNReal.ofReal (cw t) *
              ENNReal.ofReal (Real.exp (-((4 * Real.pi ^ 2 * ‖ξ - η‖ ^ 2) * t)))) := by
          intro t
          rw [mul_left_comm]
          congr 3
          ring
        simp_rw [e1]
        rw [lintegral_const_mul' _ _ enorm_ne_top]

/-- `C₀`: the constant of the Riesz kernel's Fourier majorant `C₀ |w|^{-(d-s)}` -/
def tc3_C0 (d : ℕ) (s : ℝ) : ℝ :=
  aDS d s * (Real.Gamma (((d : ℝ) - s) / 2) * (4 * Real.pi ^ 2) ^ (-(((d : ℝ) - s) / 2)))

theorem tc3_t_lintegral {β c r : ℝ} (hβ : 0 < β) (hc : 0 ≤ c) (hr : 0 < r) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (c * t ^ (β - 1)) * ENNReal.ofReal (Real.exp (-(r * t))) =
      ENNReal.ofReal (c * ((1 / r) ^ β * Real.Gamma β)) := by
  have hint : IntegrableOn (fun t : ℝ => t ^ (β - 1) * Real.exp (-(r * t))) (Ioi (0 : ℝ)) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := β - 1) (b := r)
      (by linarith) one_pos hr
    refine this.congr_fun (fun l hl => ?_) measurableSet_Ioi
    simp only [Real.rpow_one]
    rw [neg_mul]
  have hnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ c * (t ^ (β - 1) * Real.exp (-(r * t))) := by
    intro t ht
    have : 0 < t := ht
    positivity
  calc ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (c * t ^ (β - 1)) * ENNReal.ofReal (Real.exp (-(r * t)))
      = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (c * (t ^ (β - 1) * Real.exp (-(r * t)))) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        have : 0 < t := ht
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
    _ = ENNReal.ofReal (∫ t in Ioi (0 : ℝ), c * (t ^ (β - 1) * Real.exp (-(r * t)))) :=
        (ofReal_integral_eq_lintegral_ofReal (hint.const_mul c)
          ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hnn))).symm
    _ = _ := by
        rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hβ hr]

theorem tc3_kernel_eq {s : ℝ} (hs : 0 < s) (w : Euc d) (hw : w ≠ 0) :
    aDS d s * ((1 / (4 * Real.pi ^ 2 * ‖w‖ ^ 2)) ^ (((d : ℝ) - s) / 2) *
      Real.Gamma (((d : ℝ) - s) / 2)) = tc3_C0 d s * ‖w‖ ^ (-((d : ℝ) - s)) := by
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hp : 0 < 4 * Real.pi ^ 2 := by positivity
  have e1 : (1 / (4 * Real.pi ^ 2 * ‖w‖ ^ 2)) ^ (((d : ℝ) - s) / 2) =
      (4 * Real.pi ^ 2) ^ (-(((d : ℝ) - s) / 2)) * ‖w‖ ^ (-((d : ℝ) - s)) := by
    rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity),
      Real.mul_rpow hp.le (by positivity)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    congr 1
    push_cast
    ring
  rw [e1, tc3_C0]
  ring

theorem tc3_Ghat_enorm_le {θ : Euc d → ℝ} (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    {s : ℝ} (hs : 0 < s) (hsd : s < d) (ξ : Euc d) :
    ‖tc3_Ghat (tc3_Gloc d s θ) ξ‖ₑ ≤ ∫⁻ η : Euc d,
      ‖(𝓕 (sobmul_T θ hθ hc) : SchwartzMap (Euc d) ℂ) η‖ₑ *
        ENNReal.ofReal (tc3_C0 d s * ‖ξ - η‖ ^ (-((d : ℝ) - s))) := by
  have hβ : 0 < ((d : ℝ) - s) / 2 := by linarith
  have haDS := psd3_aDS_pos (d := d) hs
  have hd : 0 < d := by
    have : (0 : ℝ) < d := lt_trans hs hsd
    exact_mod_cast this
  have : Nontrivial (Euc d) := by
    rw [← Module.finrank_pos_iff (R := ℝ)]; simpa using hd
  have hx0 : ∀ᵐ x ∂(volume : Measure (Euc d)), x ≠ 0 := by
    rw [ae_iff]
    simpa using measure_singleton (μ := (volume : Measure (Euc d))) (0 : Euc d)
  have hmeas : Measurable (fun t : ℝ => aDS d s * t ^ (((d : ℝ) - s) / 2 - 1)) :=
    measurable_const.mul (measurable_id.pow_const _)
  have h := tc3_Ghat_enorm_gen hθ hc (cw := fun t : ℝ => aDS d s * t ^ (((d : ℝ) - s) / 2 - 1))
    hmeas (fun t ht => by positivity) (K := rieszKernel d s)
    (by
      filter_upwards with x
      rw [rieszKernel_eq hs.ne', tc3_riesz_rep hs x]
      rfl)
    (by
      filter_upwards [hx0] with x hx
      exact tc3_psdF_integrableOn hs hx)
    (tc3_Gloc_integrable hθ.continuous hc hs.le hsd) ξ
  refine h.trans (lintegral_mono_ae ?_)
  have hne : ∀ᵐ η ∂(volume : Measure (Euc d)), η ≠ ξ := by
    rw [ae_iff]
    simpa using measure_singleton (μ := (volume : Measure (Euc d))) ξ
  filter_upwards [hne] with η hη
  have hw : ξ - η ≠ 0 := sub_ne_zero.2 (Ne.symm hη)
  have hr : 0 < 4 * Real.pi ^ 2 * ‖ξ - η‖ ^ 2 := by
    have := norm_pos_iff.2 hw
    positivity
  rw [tc3_t_lintegral hβ (by positivity) hr, tc3_kernel_eq hs (ξ - η) hw]

/-! ### A Peetre-type convolution bound against `|z|^{-γ}` -/

theorem tc3_pt1 {γ : ℝ} (hγ : 0 < γ) {z : ℝ} (hz : 0 < z) :
    (1 + z) ^ γ * z ^ (-γ) ≤ 2 ^ γ * (1 + z ^ (-γ)) := by
  have h1 : (1 + z) ^ γ ≤ 2 ^ γ * (1 + z ^ γ) := by
    have hzg : 0 < z ^ γ := Real.rpow_pos_of_pos hz _
    by_cases hz1 : z ≤ 1
    · calc (1 + z) ^ γ ≤ 2 ^ γ := Real.rpow_le_rpow (by positivity) (by linarith) hγ.le
        _ ≤ 2 ^ γ * (1 + z ^ γ) := by
          have : (0 : ℝ) < 2 ^ γ := by positivity
          nlinarith
    · push_neg at hz1
      calc (1 + z) ^ γ ≤ (2 * z) ^ γ := Real.rpow_le_rpow (by positivity) (by linarith) hγ.le
        _ = 2 ^ γ * z ^ γ := Real.mul_rpow (by norm_num) hz.le
        _ ≤ 2 ^ γ * (1 + z ^ γ) := by
          have : (0 : ℝ) < 2 ^ γ := by positivity
          nlinarith
  have hzn : 0 ≤ z ^ (-γ) := (Real.rpow_pos_of_pos hz _).le
  have e : z ^ γ * z ^ (-γ) = 1 := by
    rw [← Real.rpow_add hz]; simp
  calc (1 + z) ^ γ * z ^ (-γ) ≤ 2 ^ γ * (1 + z ^ γ) * z ^ (-γ) := by gcongr
    _ = 2 ^ γ * (z ^ (-γ) + z ^ γ * z ^ (-γ)) := by ring
    _ = 2 ^ γ * (1 + z ^ (-γ)) := by rw [e]; ring

theorem tc3_pt2 {γ : ℝ} (hγ : 0 < γ) {w K1 z Φ : ℝ} (hw : 0 ≤ w) (hK1 : z ≤ 1 → w ≤ K1)
    (hΦ : Φ = if z ≤ 1 then z ^ (-γ) else 0) (hz : 0 < z) :
    w * z ^ (-γ) ≤ K1 * Φ + w := by
  have hzn : 0 < z ^ (-γ) := Real.rpow_pos_of_pos hz _
  by_cases hz1 : z ≤ 1
  · rw [if_pos hz1] at hΦ
    rw [hΦ]
    nlinarith [hK1 hz1]
  · push_neg at hz1
    rw [if_neg (not_le.2 hz1)] at hΦ
    have : z ^ (-γ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hz1.le (by linarith)
    rw [hΦ]
    nlinarith

theorem tc3_peetre {γ : ℝ} (hγ : 0 < γ) (hγd : γ < d) {a : Euc d → ℂ} {K1 : ℝ}
    (hK1 : ∀ η, ‖a η‖ * (1 + ‖η‖) ^ γ ≤ K1)
    (hint : Integrable (fun η => ‖a η‖ * (1 + ‖η‖) ^ γ) volume) (ξ : Euc d) :
    ∫⁻ η : Euc d, ‖a η‖ₑ * ENNReal.ofReal (‖ξ - η‖ ^ (-γ)) ≤
      ENNReal.ofReal (2 ^ γ * (1 + ‖ξ‖) ^ (-γ) *
        (2 * (∫ η, ‖a η‖ * (1 + ‖η‖) ^ γ) +
          K1 * ∫ z in Metric.closedBall (0 : Euc d) 1, ‖z‖ ^ (-γ))) := by
  set w : Euc d → ℝ := fun η => ‖a η‖ * (1 + ‖η‖) ^ γ with hw
  set Φ : Euc d → ℝ := (Metric.closedBall (0 : Euc d) 1).indicator (fun z => ‖z‖ ^ (-γ)) with hΦ
  have hwnn : ∀ η, 0 ≤ w η := fun η => by simp only [hw]; positivity
  have hK1nn : 0 ≤ K1 := le_trans (hwnn 0) (hK1 0)
  have hlocI : IntegrableOn (fun z : Euc d => ‖z‖ ^ (-γ)) (Metric.closedBall 0 1) volume := by
    have := (rieszKernel_locallyIntegrable hγ.le hγd).integrableOn_isCompact
      (isCompact_closedBall (0 : Euc d) 1)
    exact this.congr_fun (fun z _ => rieszKernel_eq hγ.ne' z) measurableSet_closedBall
  have hΦi : Integrable Φ volume := (integrable_indicator_iff measurableSet_closedBall).2 hlocI
  have hΦnn : ∀ z, 0 ≤ Φ z := fun z => by
    simp only [hΦ, Set.indicator]; split_ifs <;> positivity
  have hshift : Integrable (fun η => Φ (ξ - η)) volume := hΦi.comp_sub_left ξ
  set F : Euc d → ℝ := fun η => 2 ^ γ * (1 + ‖ξ‖) ^ (-γ) * (2 * w η + K1 * Φ (ξ - η)) with hF
  have hFi : Integrable F volume := ((hint.const_mul 2).add (hshift.const_mul K1)).const_mul _
  have hFnn : ∀ η, 0 ≤ F η := fun η => by
    have := hwnn η
    have := hΦnn (ξ - η)
    simp only [hF]; positivity
  have hpt : ∀ η, ‖a η‖ₑ * ENNReal.ofReal (‖ξ - η‖ ^ (-γ)) ≤ ENNReal.ofReal (F η) := by
    intro η
    rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    set z : ℝ := ‖ξ - η‖ with hz
    by_cases hz0 : z = 0
    · rw [hz0, Real.zero_rpow (neg_ne_zero.2 hγ.ne'), mul_zero]
      exact hFnn η
    have hzpos : 0 < z := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz0)
    have hP : 1 + ‖ξ‖ ≤ (1 + ‖η‖) * (1 + z) := by
      have h1 : ‖ξ‖ ≤ ‖η‖ + z := by
        have := norm_add_le η (ξ - η)
        simpa [hz] using this
      nlinarith [norm_nonneg η, hzpos]
    have hA : 0 < (1 + ‖ξ‖) ^ γ := by positivity
    have h4 : (1 + ‖ξ‖) ^ γ ≤ (1 + ‖η‖) ^ γ * (1 + z) ^ γ := by
      rw [← Real.mul_rpow (by positivity) (by positivity)]
      exact Real.rpow_le_rpow (by positivity) hP hγ.le
    have hpt1 := tc3_pt1 hγ hzpos
    have hpt2 := tc3_pt2 (K1 := K1) (Φ := Φ (ξ - η)) hγ (hwnn η) (fun h => hK1 η)
      (by
        simp only [hΦ, Set.indicator, Metric.mem_closedBall, dist_zero_right]
        rfl) hzpos
    have hzn : 0 ≤ z ^ (-γ) := (Real.rpow_pos_of_pos hzpos _).le
    have key : ‖a η‖ * z ^ (-γ) * (1 + ‖ξ‖) ^ γ ≤ 2 ^ γ * (2 * w η + K1 * Φ (ξ - η)) := by
      calc ‖a η‖ * z ^ (-γ) * (1 + ‖ξ‖) ^ γ
          ≤ ‖a η‖ * z ^ (-γ) * ((1 + ‖η‖) ^ γ * (1 + z) ^ γ) := by gcongr
        _ = w η * ((1 + z) ^ γ * z ^ (-γ)) := by simp only [hw]; ring
        _ ≤ w η * (2 ^ γ * (1 + z ^ (-γ))) := by gcongr
        _ = 2 ^ γ * (w η + w η * z ^ (-γ)) := by ring
        _ ≤ 2 ^ γ * (2 * w η + K1 * Φ (ξ - η)) := by
          have : (0 : ℝ) < 2 ^ γ := by positivity
          nlinarith
    have h5 := (le_div_iff₀ hA).2 key
    refine h5.trans (le_of_eq ?_)
    simp only [hF]
    rw [Real.rpow_neg (by positivity)]
    field_simp
  calc ∫⁻ η : Euc d, ‖a η‖ₑ * ENNReal.ofReal (‖ξ - η‖ ^ (-γ))
      ≤ ∫⁻ η, ENNReal.ofReal (F η) := lintegral_mono hpt
    _ = ENNReal.ofReal (∫ η, F η) :=
        (ofReal_integral_eq_lintegral_ofReal hFi (Filter.Eventually.of_forall hFnn)).symm
    _ = _ := by
        congr 1
        simp only [hF]
        rw [integral_const_mul, integral_add (hint.const_mul 2) (hshift.const_mul K1),
          integral_const_mul, integral_const_mul, integral_sub_left_eq_self Φ volume ξ,
          hΦ, integral_indicator measurableSet_closedBall]

theorem tc3_schwartz_weight (a : SchwartzMap (Euc d) ℂ) {γ : ℝ} (hγ : 0 ≤ γ) :
    (∃ K1 : ℝ, ∀ η, ‖a η‖ * (1 + ‖η‖) ^ γ ≤ K1) ∧
      Integrable (fun η => ‖a η‖ * (1 + ‖η‖) ^ γ) volume := by
  set m : ℕ := ⌈γ⌉₊ with hm
  have hpt : ∀ η : Euc d, ‖a η‖ * (1 + ‖η‖) ^ γ ≤ 2 ^ m * (‖a η‖ + ‖η‖ ^ m * ‖a η‖) := by
    intro η
    have hr : 0 ≤ ‖η‖ := norm_nonneg _
    have h1 : (1 + ‖η‖) ^ γ ≤ (1 + ‖η‖) ^ (m : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (Nat.le_ceil γ)
    rw [Real.rpow_natCast] at h1
    have h2 : (1 + ‖η‖) ^ m ≤ 2 ^ m * (1 + ‖η‖ ^ m) := by
      have h2m : (0 : ℝ) < 2 ^ m := by positivity
      have hrm : 0 ≤ ‖η‖ ^ m := pow_nonneg hr m
      by_cases hr1 : ‖η‖ ≤ 1
      · calc (1 + ‖η‖) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
          _ ≤ 2 ^ m * (1 + ‖η‖ ^ m) := by nlinarith
      · push_neg at hr1
        calc (1 + ‖η‖) ^ m ≤ (2 * ‖η‖) ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
          _ = 2 ^ m * ‖η‖ ^ m := mul_pow _ _ _
          _ ≤ 2 ^ m * (1 + ‖η‖ ^ m) := by nlinarith
    calc ‖a η‖ * (1 + ‖η‖) ^ γ ≤ ‖a η‖ * (2 ^ m * (1 + ‖η‖ ^ m)) := by
          gcongr; exact h1.trans h2
      _ = 2 ^ m * (‖a η‖ + ‖η‖ ^ m * ‖a η‖) := by ring
  refine ⟨⟨2 ^ m * (SchwartzMap.seminorm ℝ 0 0 a + SchwartzMap.seminorm ℝ m 0 a), fun η => ?_⟩, ?_⟩
  · refine (hpt η).trans ?_
    have h1 := SchwartzMap.norm_le_seminorm ℝ a η
    have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ a m η
    gcongr
  · refine Integrable.mono' (((a.integrable (μ := volume)).norm.add
      (a.integrable_pow_mul volume m)).const_mul (2 ^ m)) ?_ (Filter.Eventually.of_forall fun η => ?_)
    · exact ((a.continuous.norm).mul (Continuous.rpow_const (by fun_prop)
        (fun x => Or.inl (by positivity)))).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (by positivity)]
      exact hpt η

theorem tc3_peetre_wt {γ : ℝ} (hγ : 0 < γ) (ξ : Euc d) :
    (1 + ‖ξ‖) ^ (-γ) ≤ (2 * Real.pi) ^ γ * wt ξ ^ (-γ / 2) := by
  have hr : 0 ≤ ‖ξ‖ := norm_nonneg _
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hwt : wt ξ ≤ (2 * Real.pi * (1 + ‖ξ‖)) ^ 2 := by
    unfold wt
    nlinarith [sq_nonneg ‖ξ‖, Real.pi_gt_three, mul_nonneg hr (by positivity : (0:ℝ) ≤ Real.pi ^ 2)]
  have hM : 0 < 2 * Real.pi * (1 + ‖ξ‖) := by positivity
  have h1 : ((2 * Real.pi * (1 + ‖ξ‖)) ^ 2) ^ (-γ / 2) ≤ wt ξ ^ (-γ / 2) :=
    Real.rpow_le_rpow_of_nonpos (wt_pos ξ) hwt (by linarith)
  have h2 : ((2 * Real.pi * (1 + ‖ξ‖)) ^ 2) ^ (-γ / 2) = (2 * Real.pi * (1 + ‖ξ‖)) ^ (-γ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
    congr 1
    push_cast
    ring
  rw [h2, Real.mul_rpow (by positivity) (by positivity)] at h1
  have h3 : (2 * Real.pi) ^ γ * (2 * Real.pi) ^ (-γ) = 1 := by
    rw [← Real.rpow_add (by positivity)]; simp
  calc (1 + ‖ξ‖) ^ (-γ) = (2 * Real.pi) ^ γ * ((2 * Real.pi) ^ (-γ) * (1 + ‖ξ‖) ^ (-γ)) := by
        rw [← mul_assoc, h3, one_mul]
    _ ≤ (2 * Real.pi) ^ γ * wt ξ ^ (-γ / 2) := by gcongr

/-- **Fourier decay of the localised Riesz kernel** (`0 < s < d`, `θ ∈ C_c^∞`):
`|\widehat{θ g}(ξ)| ≤ A ⟨ξ⟩^{-(d-s)}` where `⟨ξ⟩² = wt ξ`. -/
theorem tc3_riesz_loc_decay {θ : Euc d → ℝ} (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    {s : ℝ} (hs : 0 < s) (hsd : s < d) :
    ∃ A : ℝ, 0 < A ∧ ∀ ξ : Euc d,
      ‖tc3_Ghat (tc3_Gloc d s θ) ξ‖ ≤ A * wt ξ ^ (-((d : ℝ) - s) / 2) := by
  set γ : ℝ := (d : ℝ) - s with hγdef
  have hγ : 0 < γ := by rw [hγdef]; linarith
  have hγd : γ < d := by rw [hγdef]; linarith
  set a : SchwartzMap (Euc d) ℂ := 𝓕 (sobmul_T θ hθ hc) with ha
  obtain ⟨⟨K1, hK1⟩, hint⟩ := tc3_schwartz_weight a hγ.le
  set W : ℝ := ∫ η, ‖a η‖ * (1 + ‖η‖) ^ γ with hW
  set J : ℝ := ∫ z in Metric.closedBall (0 : Euc d) 1, ‖z‖ ^ (-γ) with hJ
  have hW0 : 0 ≤ W := integral_nonneg fun η => by positivity
  have hJ0 : 0 ≤ J := setIntegral_nonneg measurableSet_closedBall fun z _ => by positivity
  have hK10 : 0 ≤ K1 := le_trans (by positivity) (hK1 0)
  have hC0 : 0 ≤ tc3_C0 d s := by
    have := psd3_aDS_pos (d := d) hs
    have hG : 0 < Real.Gamma (((d : ℝ) - s) / 2) := Real.Gamma_pos_of_pos (by linarith)
    unfold tc3_C0
    positivity
  set B : ℝ := tc3_C0 d s * (2 ^ γ * (2 * W + K1 * J)) with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  refine ⟨(B + 1) * (2 * Real.pi) ^ γ, by positivity, fun ξ => ?_⟩
  have h1 : ‖tc3_Ghat (tc3_Gloc d s θ) ξ‖ₑ ≤ ∫⁻ η : Euc d,
      ‖a η‖ₑ * ENNReal.ofReal (tc3_C0 d s * ‖ξ - η‖ ^ (-γ)) := tc3_Ghat_enorm_le hθ hc hs hsd ξ
  have h2 := tc3_peetre hγ hγd hK1 hint ξ
  have h3 : ‖tc3_Ghat (tc3_Gloc d s θ) ξ‖ₑ ≤ ENNReal.ofReal (B * (1 + ‖ξ‖) ^ (-γ)) := by
    refine h1.trans ?_
    have e : ∀ η : Euc d, ‖a η‖ₑ * ENNReal.ofReal (tc3_C0 d s * ‖ξ - η‖ ^ (-γ)) =
        ENNReal.ofReal (tc3_C0 d s) * (‖a η‖ₑ * ENNReal.ofReal (‖ξ - η‖ ^ (-γ))) := by
      intro η
      rw [ENNReal.ofReal_mul hC0, mul_left_comm]
    simp_rw [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul_right h2 _).trans_eq ?_
    rw [← ENNReal.ofReal_mul hC0]
    congr 1
    rw [hB]
    ring
  rw [← ofReal_norm] at h3
  have h4 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
  refine h4.trans ?_
  have h5 := tc3_peetre_wt hγ ξ
  calc B * (1 + ‖ξ‖) ^ (-γ) ≤ (B + 1) * (1 + ‖ξ‖) ^ (-γ) := by
        gcongr; linarith
    _ ≤ (B + 1) * ((2 * Real.pi) ^ γ * wt ξ ^ (-γ / 2)) := by gcongr
    _ = (B + 1) * (2 * Real.pi) ^ γ * wt ξ ^ (-((d : ℝ) - s) / 2) := by
        rw [hγdef]; ring

end HRS.MS.Tc3
