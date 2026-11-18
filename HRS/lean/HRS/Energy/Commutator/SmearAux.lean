import HRS.Energy.Commutator.Slice

/-!
# Auxiliary lemmas for `Smear.lean` (packet CM-S2)

Radial Green identity (the weak form of `(l - Δ) u = σ` for a radial profile `u(x) = Γ(max(|x|, η))`):
polar coordinates (`polar_integral`), the integration by parts for the Lipschitz radial function
`u` obtained by a ramp regularisation (`ibp_lip`), and the one-dimensional integration by parts
(`core_1d`), assembled in `core_weak`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators
noncomputable section
namespace HRS.Commutator.SmearAux
variable {d : ℕ}

abbrev sphMeas (d : ℕ) : Measure (sphere (0 : Euc d) 1) := (volume : Measure (Euc d)).toSphere

theorem polar_prod_integrable (hd : 1 ≤ d) {F : Euc d → ℝ} (hF : Integrable F) :
    Integrable (fun p : sphere (0 : Euc d) 1 × Ioi (0:ℝ) => F ((p.2 : ℝ) • (p.1 : Euc d)))
      ((sphMeas d).prod (Measure.volumeIoiPow (Module.finrank ℝ (Euc d) - 1))) := by
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hmp := (volume : Measure (Euc d)).measurePreserving_homeomorphUnitSphereProd
  have hemb := (homeomorphUnitSphereProd (Euc d)).measurableEmbedding
  have h1 : Integrable (fun x : ({0}ᶜ : Set (Euc d)) => F x) ((volume : Measure (Euc d)).comap (↑)) := by
    exact (integrableOn_iff_comap_subtypeVal (measurableSet_singleton _).compl).1 hF.integrableOn
  have := hmp.integrable_comp_emb hemb (g := fun p : sphere (0 : Euc d) 1 × Ioi (0:ℝ) => F ((p.2 : ℝ) • (p.1 : Euc d)))
  rw [← this]
  refine h1.congr (Eventually.of_forall fun x => ?_)
  simp only [Function.comp, homeomorphUnitSphereProd_apply_snd_coe, homeomorphUnitSphereProd_apply_fst_coe]
  have : (x : Euc d) ≠ 0 := x.2
  congr 1
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 this), one_smul]

theorem polar_integral (hd : 1 ≤ d) {F : Euc d → ℝ} (hF : Integrable F) :
    ∫ y, F y = ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * ∫ ω, F (r • (ω : Euc d)) ∂(sphMeas d) := by
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hfr : Module.finrank ℝ (Euc d) = d := by simp
  have hmp := (volume : Measure (Euc d)).measurePreserving_homeomorphUnitSphereProd
  have hemb := (homeomorphUnitSphereProd (Euc d)).measurableEmbedding
  have e1 : ∫ y, F y = ∫ x : ({0}ᶜ : Set (Euc d)), F x ∂((volume : Measure (Euc d)).comap (↑)) := by
    rw [integral_subtype_comap (measurableSet_singleton _).compl fun x => F x, restrict_compl_singleton]
  rw [e1]
  set G : sphere (0 : Euc d) 1 × Ioi (0:ℝ) → ℝ := fun p => F ((p.2 : ℝ) • (p.1 : Euc d)) with hG
  have e2 : ∫ x : ({0}ᶜ : Set (Euc d)), F x ∂((volume : Measure (Euc d)).comap (↑)) =
      ∫ p, G p ∂((sphMeas d).prod (Measure.volumeIoiPow (Module.finrank ℝ (Euc d) - 1))) := by
    rw [← hmp.integral_comp hemb G]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hG, homeomorphUnitSphereProd_apply_snd_coe, homeomorphUnitSphereProd_apply_fst_coe]
    have : (x : Euc d) ≠ 0 := x.2
    congr 1
    rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 this), one_smul]
  rw [e2]
  have hint : Integrable G ((sphMeas d).prod (Measure.volumeIoiPow (Module.finrank ℝ (Euc d) - 1))) :=
    polar_prod_integrable hd hF
  rw [integral_prod_symm _ hint]
  rw [hfr]
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul]
  · have := integral_subtype_comap (μ := (volume : Measure ℝ)) (s := Ioi (0:ℝ)) measurableSet_Ioi fun a : ℝ => Real.toNNReal (a ^ (d - 1)) • ∫ ω, F (a • (ω : Euc d)) ∂(sphMeas d)
    simp only [hG]
    rw [this]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hx.out.le _)]
    rfl
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

theorem polar_integrableOn (hd : 1 ≤ d) {F : Euc d → ℝ} (hF : Integrable F) :
    IntegrableOn (fun r : ℝ => r ^ (d - 1) * ∫ ω, F (r • (ω : Euc d)) ∂(sphMeas d)) (Ioi 0) := by
  have hint := polar_prod_integrable hd hF
  have h2 := hint.integral_prod_right
  have hfr : Module.finrank ℝ (Euc d) = d := by simp
  rw [hfr] at h2
  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioi]
  simp only [Measure.volumeIoiPow] at h2
  rw [integrable_withDensity_iff_integrable_smul'] at h2
  · refine h2.congr (Eventually.of_forall fun x => ?_)
    simp only [Function.comp, smul_eq_mul]
    rw [ENNReal.toReal_ofReal (pow_nonneg x.2.out.le _)]
  · fun_prop
  · simp

/-- the piecewise linear ramp from `0` (at `η`) to `1` (at `η + ε`) -/
def ramp (η ε r : ℝ) : ℝ := max 0 (min 1 ((r - η) / ε))

theorem continuous_ramp (η ε : ℝ) : Continuous (ramp η ε) := by
  unfold ramp; fun_prop

theorem ramp_nonneg (η ε r : ℝ) : 0 ≤ ramp η ε r := le_max_left _ _

theorem ramp_le_one (η ε r : ℝ) : ramp η ε r ≤ 1 := by
  unfold ramp; exact max_le zero_le_one (min_le_left _ _)

theorem ramp_of_le {η ε r : ℝ} (hε : 0 < ε) (h : r ≤ η) : ramp η ε r = 0 := by
  unfold ramp
  have : (r - η) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  rw [max_eq_left]; exact (min_le_right _ _).trans this

theorem ramp_of_ge {η ε r : ℝ} (hε : 0 < ε) (h : η + ε ≤ r) : ramp η ε r = 1 := by
  unfold ramp
  have : 1 ≤ (r - η) / ε := by rw [le_div_iff₀ hε]; linarith
  rw [min_eq_left this, max_eq_right zero_le_one]

theorem tendsto_ramp {η r : ℝ} (hr : η < r) : Tendsto (fun ε => ramp η ε r) (𝓝[>] 0) (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < r - η by linarith)] with ε hε
  exact (ramp_of_ge hε.1 (by linarith [hε.2])).symm

/-- the smoothed radial profile `H_ε(r) = ∫_η^r Γ' χ_ε`. -/
def Hrad (Γ' : ℝ → ℝ) (η ε r : ℝ) : ℝ := ∫ s in η..r, Γ' s * ramp η ε s

theorem continuous_gε {Γ' : ℝ → ℝ} {η : ℝ} (hη : 0 < η) (hc : ∀ r, 0 < r → ContinuousAt Γ' r)
    {ε : ℝ} (hε : 0 < ε) : Continuous fun s => Γ' s * ramp η ε s := by
  rw [continuous_iff_continuousAt]
  intro s
  by_cases hs : 0 < s
  · exact (hc s hs).mul (continuous_ramp η ε).continuousAt
  · have : (fun s => Γ' s * ramp η ε s) =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds (show s < η by linarith [not_lt.1 hs])] with t ht
      rw [ramp_of_le hε ht.out.le, mul_zero]
    exact continuousAt_const.congr this.symm

theorem hasDerivAt_Hrad {Γ' : ℝ → ℝ} {η : ℝ} (hη : 0 < η) (hc : ∀ r, 0 < r → ContinuousAt Γ' r)
    {ε : ℝ} (hε : 0 < ε) (r : ℝ) : HasDerivAt (Hrad Γ' η ε) (Γ' r * ramp η ε r) r :=
  ((continuous_gε hη hc hε).integral_hasStrictDerivAt η r).hasDerivAt

theorem Hrad_of_le {Γ' : ℝ → ℝ} {η ε r : ℝ} (hε : 0 < ε) (hr : r ≤ η) : Hrad Γ' η ε r = 0 := by
  unfold Hrad
  rw [intervalIntegral.integral_symm]
  have : ∫ s in r..η, Γ' s * ramp η ε s = 0 := by
    rw [intervalIntegral.integral_of_le hr]
    refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
    rw [ramp_of_le hε hs.2, mul_zero]
  rw [this, neg_zero]

theorem abs_Hrad_le {Γ' : ℝ → ℝ} {η ε r C : ℝ} (hε : 0 < ε) (hC : ∀ s, η ≤ s → |Γ' s| ≤ C)
    (hη : 0 < η) (hc : ∀ r, 0 < r → ContinuousAt Γ' r) (hr : η ≤ r) :
    |Hrad Γ' η ε r| ≤ C * (r - η) := by
  unfold Hrad
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := η) (b := r) (C := C)
    (f := fun s => Γ' s * ramp η ε s) (by
      intro s hs
      rw [Set.uIoc_of_le hr] at hs
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ramp_nonneg _ _ _)]
      calc |Γ' s| * ramp η ε s ≤ C * 1 := by
            have := hC s hs.1.le
            exact mul_le_mul this (ramp_le_one _ _ _) (ramp_nonneg _ _ _) ((abs_nonneg _).trans this)
        _ = C := mul_one C)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ r - η)] at this
  exact this


theorem hasFDerivAt_norm_of_ne {x : Euc d} (hx : x ≠ 0) :
    HasFDerivAt (fun y : Euc d => ‖y‖) (‖x‖⁻¹ • innerSL ℝ x) x := by
  have h1 := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hx2 : ‖x‖ ^ 2 ≠ 0 := by positivity
  have h2 := h1.sqrt hx2
  have e : (fun y : Euc d => √(‖y‖ ^ 2)) = fun y => ‖y‖ := by
    funext y; exact Real.sqrt_sq (norm_nonneg y)
  rw [e] at h2
  convert h2 using 1
  rw [Real.sqrt_sq (norm_nonneg x)]
  ext v
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, nsmul_eq_mul]
  have : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  field_simp
  norm_num

/-- the smooth radial function `u_ε(x) = Γ(η) + H_ε(|x|)` -/
def uε (Γ Γ' : ℝ → ℝ) (η ε : ℝ) (x : Euc d) : ℝ := Γ η + Hrad Γ' η ε ‖x‖

theorem hasFDerivAt_uε {Γ Γ' : ℝ → ℝ} {η : ℝ} (hη : 0 < η) (hc : ∀ r, 0 < r → ContinuousAt Γ' r)
    {ε : ℝ} (hε : 0 < ε) (x : Euc d) :
    HasFDerivAt (uε Γ Γ' η ε) ((‖x‖⁻¹ * (Γ' ‖x‖ * ramp η ε ‖x‖)) • innerSL ℝ x) x := by
  by_cases hx : x = 0
  · subst hx
    have : (uε Γ Γ' η ε) =ᶠ[𝓝 (0 : Euc d)] fun _ => Γ η := by
      filter_upwards [Metric.ball_mem_nhds (0 : Euc d) hη] with y hy
      unfold uε
      rw [Hrad_of_le hε (by simpa using hy.out.le), add_zero]
    simp only [norm_zero, inv_zero, zero_mul, zero_smul]
    exact (hasFDerivAt_const (Γ η) (0 : Euc d)).congr_of_eventuallyEq this
  · have h1 := (hasDerivAt_Hrad hη hc hε ‖x‖).comp_hasFDerivAt x (hasFDerivAt_norm_of_ne hx)
    have h2 := h1.const_add (Γ η)
    refine (show HasFDerivAt (uε Γ Γ' η ε) _ x from h2).congr_fderiv ?_
    rw [smul_smul, mul_comm]


/-- the coordinate vector `e_i` -/
def ei (i : Fin d) : Euc d := EuclideanSpace.single i 1

/-- the second directional derivative `∂_i ∂_i φ` -/
def dd (φ : Euc d → ℝ) (i : Fin d) (y : Euc d) : ℝ :=
  fderiv ℝ (fun x => fderiv ℝ φ x (ei i)) y (ei i)

/-- the Laplacian `Δφ = ∑ ∂_i ∂_i φ` -/
def lap (φ : Euc d → ℝ) (y : Euc d) : ℝ := ∑ i, dd φ i y

/-- admissible test functions: `C²` with weighted integrable derivatives and bounded gradient. -/
structure TF (φ : Euc d → ℝ) : Prop where
  c2 : ContDiff ℝ 2 φ
  i0 : Integrable (fun y => (1 + ‖y‖) * |φ y|)
  i1 : Integrable (fun y => (1 + ‖y‖) * ‖fderiv ℝ φ y‖)
  i2 : ∀ i, Integrable (fun y => (1 + ‖y‖) * |dd φ i y|)
  bd : ∃ K, ∀ y, ‖fderiv ℝ φ y‖ ≤ K

theorem integrable_of_weighted {f : Euc d → ℝ} (hc : Continuous f)
    (h : Integrable (fun y => (1 + ‖y‖) * |f y|)) : Integrable f := by
  refine Integrable.mono' h hc.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  have : (1:ℝ) ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
  nlinarith [abs_nonneg (f y)]


theorem abs_apply_le_norm (x : Euc d) (i : Fin d) : |x i| ≤ ‖x‖ := by
  have := PiLp.norm_apply_le x i
  simpa [Real.norm_eq_abs] using this

namespace TF
variable {φ : Euc d → ℝ}

theorem cont (h : TF φ) : Continuous φ := h.c2.continuous

theorem contDiff_fderiv (h : TF φ) : ContDiff ℝ 1 (fderiv ℝ φ) :=
  h.c2.fderiv_right (by norm_num)

theorem cont_fderiv (h : TF φ) : Continuous (fderiv ℝ φ) := h.contDiff_fderiv.continuous

theorem contDiff_g (h : TF φ) (i : Fin d) : ContDiff ℝ 1 (fun x => fderiv ℝ φ x (ei i)) :=
  h.contDiff_fderiv.clm_apply contDiff_const

theorem cont_g (h : TF φ) (i : Fin d) : Continuous (fun x => fderiv ℝ φ x (ei i)) :=
  (h.contDiff_g i).continuous

theorem diff_g (h : TF φ) (i : Fin d) : Differentiable ℝ (fun x => fderiv ℝ φ x (ei i)) :=
  (h.contDiff_g i).differentiable one_ne_zero

theorem cont_dd (h : TF φ) (i : Fin d) : Continuous (dd φ i) := by
  unfold dd
  have := (h.contDiff_g i).continuous_fderiv one_ne_zero
  exact this.clm_apply continuous_const

theorem integrable_phi (h : TF φ) : Integrable φ := integrable_of_weighted h.cont h.i0

theorem integrable_fderiv (h : TF φ) : Integrable (fun y => ‖fderiv ℝ φ y‖) := by
  refine Integrable.mono' h.i1 h.cont_fderiv.norm.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have : (1:ℝ) ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
  nlinarith [norm_nonneg (fderiv ℝ φ y)]

theorem abs_g_le (h : TF φ) (i : Fin d) (y : Euc d) : |fderiv ℝ φ y (ei i)| ≤ ‖fderiv ℝ φ y‖ := by
  have := (fderiv ℝ φ y).le_opNorm (ei i)
  have h1 : ‖ei i‖ = 1 := by simp [ei]
  rw [h1, mul_one] at this
  simpa [Real.norm_eq_abs] using this

end TF


/-- the radial coefficient `c_ε(x)` with `∇u_ε = c_ε(x) x`. -/
def coefε (Γ' : ℝ → ℝ) (η ε : ℝ) (x : Euc d) : ℝ := ‖x‖⁻¹ * (Γ' ‖x‖ * ramp η ε ‖x‖)

theorem abs_coefε_mul_le {Γ' : ℝ → ℝ} {η ε C : ℝ} (hη : 0 < η) (hε : 0 < ε)
    (hC : ∀ s, η ≤ s → |Γ' s| ≤ C) (x : Euc d) (i : Fin d) :
    |coefε Γ' η ε x * x i| ≤ C := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC η le_rfl)
  by_cases hx : ‖x‖ ≤ η
  · unfold coefε
    rw [ramp_of_le hε hx]
    simpa using hC0
  · push_neg at hx
    have hpos : 0 < ‖x‖ := by linarith
    unfold coefε
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (ramp_nonneg _ _ _), abs_inv, abs_of_pos hpos]
    have h1 := hC ‖x‖ hx.le
    have h2 := abs_apply_le_norm x i
    have h3 := ramp_le_one η ε ‖x‖
    have h4 := ramp_nonneg η ε ‖x‖
    calc ‖x‖⁻¹ * (|Γ' ‖x‖| * ramp η ε ‖x‖) * |x i|
        ≤ ‖x‖⁻¹ * (C * 1) * ‖x‖ := by
          gcongr
      _ = C := by field_simp

theorem abs_uε_le {Γ Γ' : ℝ → ℝ} {η ε C : ℝ} (hη : 0 < η) (hε : 0 < ε)
    (hc : ∀ r, 0 < r → ContinuousAt Γ' r) (hC : ∀ s, η ≤ s → |Γ' s| ≤ C) (x : Euc d) :
    |uε Γ Γ' η ε x| ≤ (|Γ η| + C) * (1 + ‖x‖) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC η le_rfl)
  unfold uε
  by_cases hx : ‖x‖ ≤ η
  · rw [Hrad_of_le hε hx, add_zero]
    have : (1:ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    nlinarith [abs_nonneg (Γ η)]
  · push_neg at hx
    have := abs_Hrad_le hε hC hη hc hx.le
    calc |Γ η + Hrad Γ' η ε ‖x‖| ≤ |Γ η| + |Hrad Γ' η ε ‖x‖| := abs_add_le _ _
      _ ≤ |Γ η| + C * (‖x‖ - η) := by linarith
      _ ≤ _ := by nlinarith [norm_nonneg x, abs_nonneg (Γ η)]

theorem continuous_uε {Γ Γ' : ℝ → ℝ} {η : ℝ} (hη : 0 < η) (hc : ∀ r, 0 < r → ContinuousAt Γ' r)
    {ε : ℝ} (hε : 0 < ε) : Continuous (uε Γ Γ' η ε : Euc d → ℝ) :=
  continuous_iff_continuousAt.2 fun x => (hasFDerivAt_uε hη hc hε x).continuousAt

theorem continuous_coefε {Γ' : ℝ → ℝ} {η : ℝ} (hη : 0 < η) (hc : ∀ r, 0 < r → ContinuousAt Γ' r)
    {ε : ℝ} (hε : 0 < ε) : Continuous (coefε Γ' η ε : Euc d → ℝ) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    have : (coefε Γ' η ε : Euc d → ℝ) =ᶠ[𝓝 (0 : Euc d)] fun _ => 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : Euc d) hη] with y hy
      unfold coefε
      rw [ramp_of_le hε (by simpa using hy.out.le)]
      simp
    exact continuousAt_const.congr this.symm
  · have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
    unfold coefε
    refine ContinuousAt.mul ?_ ?_
    · exact (continuous_norm.continuousAt).inv₀ hn.ne'
    · exact ContinuousAt.mul ((hc ‖x‖ hn).comp continuous_norm.continuousAt)
        ((continuous_ramp η ε).continuousAt.comp continuous_norm.continuousAt)

theorem ibp_eps {Γ Γ' : ℝ → ℝ} {η C : ℝ} (hη : 0 < η) (hc : ∀ r, 0 < r → ContinuousAt Γ' r)
    (hC : ∀ s, η ≤ s → |Γ' s| ≤ C) {ε : ℝ} (hε : 0 < ε) {φ : Euc d → ℝ} (hφ : TF φ) (i : Fin d) :
    ∫ x, uε Γ Γ' η ε x * dd φ i x =
      -∫ x, (coefε Γ' η ε x * x i) * fderiv ℝ φ x (ei i) := by
  have hfd : ∀ x, fderiv ℝ (uε Γ Γ' η ε) x (ei i) = coefε Γ' η ε x * x i := by
    intro x
    rw [(hasFDerivAt_uε hη hc hε x).fderiv]
    simp [coefε, ei, EuclideanSpace.inner_single_right]
  have hcu : Continuous (uε Γ Γ' η ε : Euc d → ℝ) := continuous_uε hη hc hε
  have hB := abs_uε_le (d := d) (Γ := Γ) hη hε hc hC
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC η le_rfl)
  have hcc : Continuous fun x : Euc d => coefε Γ' η ε x * x i :=
    (continuous_coefε hη hc hε).mul ((EuclideanSpace.proj i).continuous)
  have hW : ∀ f : Euc d → ℝ, Continuous f → Integrable (fun y => (1 + ‖y‖) * |f y|) →
      Integrable (fun x => uε Γ Γ' η ε x * f x) := by
    intro f hf hint
    refine Integrable.mono' (hint.const_mul (|Γ η| + C)) (hcu.mul hf).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |uε Γ Γ' η ε x| * |f x| ≤ ((|Γ η| + C) * (1 + ‖x‖)) * |f x| :=
          mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _)
      _ = _ := by ring
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Euc d)))
    (f := uε Γ Γ' η ε) (g := fun x => fderiv ℝ φ x (ei i)) (v := ei i) ?_ ?_ ?_
    (fun x _ => (hasFDerivAt_uε hη hc hε x).differentiableAt) (fun x _ => hφ.diff_g i x)
  · simp only [hfd] at key
    exact key
  · -- f' * g
    simp only [hfd]
    refine Integrable.mono' (hφ.integrable_fderiv.const_mul C) ?_ (Eventually.of_forall fun x => ?_)
    · exact (hcc.mul (hφ.cont_g i)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (abs_coefε_mul_le hη hε hC x i) (hφ.abs_g_le i x) (abs_nonneg _) hC0
  · -- f * g'
    exact hW _ (hφ.cont_dd i) (hφ.i2 i)
  · -- f * g
    refine hW _ (hφ.cont_g i) ?_
    refine Integrable.mono' hφ.i1 ((continuous_const.add continuous_norm).mul
      (hφ.cont_g i).abs).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith [norm_nonneg x]) (abs_nonneg _))]
    exact mul_le_mul_of_nonneg_left (hφ.abs_g_le i x) (by linarith [norm_nonneg x])


theorem sum_smul_ei (x : Euc d) : ∑ i, x i • ei i = x := by
  ext j
  simp [ei, Finset.sum_apply, Pi.single_apply]

theorem tendsto_Hrad {Γ Γ' : ℝ → ℝ} {η : ℝ} (hη : 0 < η)
    (hΓ : ∀ r, 0 < r → HasDerivAt Γ (Γ' r) r) (hc : ∀ r, 0 < r → ContinuousAt Γ' r) {C : ℝ}
    (hC : ∀ s, η ≤ s → |Γ' s| ≤ C) {r : ℝ} (hr : η < r) :
    Tendsto (fun ε => Hrad Γ' η ε r) (𝓝[>] 0) (𝓝 (Γ r - Γ η)) := by
  have hcont : ContinuousOn Γ' (Icc η r) := fun s hs =>
    (hc s (lt_of_lt_of_le hη hs.1)).continuousWithinAt
  have hft : ∫ s in η..r, Γ' s = Γ r - Γ η := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => ?_) (hcont.mono (by
      rw [Set.uIcc_of_le hr.le]) |>.intervalIntegrable)
    rw [Set.uIcc_of_le hr.le] at hs
    exact hΓ s (lt_of_lt_of_le hη hs.1)
  rw [← hft]
  unfold Hrad
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => |C|) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0:ℝ) < ε := hε
    exact (continuous_gε hη hc hε').aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0:ℝ) < ε := hε
    refine Eventually.of_forall fun s hs => ?_
    rw [Set.uIoc_of_le hr.le] at hs
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ramp_nonneg _ _ _)]
    have := hC s hs.1.le
    calc |Γ' s| * ramp η ε s ≤ |C| * 1 :=
          mul_le_mul (this.trans (le_abs_self _)) (ramp_le_one _ _ _) (ramp_nonneg _ _ _) (abs_nonneg _)
      _ = |C| := mul_one _
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun s hs => ?_
    rw [Set.uIoc_of_le hr.le] at hs
    have := (tendsto_ramp hs.1).const_mul (Γ' s)
    simpa using this


theorem tendsto_uε {Γ Γ' : ℝ → ℝ} {η : ℝ} (hη : 0 < η)
    (hΓ : ∀ r, 0 < r → HasDerivAt Γ (Γ' r) r) (hc : ∀ r, 0 < r → ContinuousAt Γ' r) {C : ℝ}
    (hC : ∀ s, η ≤ s → |Γ' s| ≤ C) (x : Euc d) :
    Tendsto (fun ε => uε Γ Γ' η ε x) (𝓝[>] 0) (𝓝 (Γ (max ‖x‖ η))) := by
  by_cases hx : ‖x‖ ≤ η
  · rw [max_eq_right hx]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0:ℝ) < ε := hε
    unfold uε
    rw [Hrad_of_le hε' hx, add_zero]
  · push_neg at hx
    rw [max_eq_left hx.le]
    have := (tendsto_Hrad hη hΓ hc hC hx).const_add (Γ η)
    simpa [uε] using this

theorem tendsto_coefε {Γ' : ℝ → ℝ} {η : ℝ} (hη : 0 < η) (x : Euc d) :
    Tendsto (fun ε => coefε Γ' η ε x) (𝓝[>] 0)
      (𝓝 (if η < ‖x‖ then ‖x‖⁻¹ * Γ' ‖x‖ else 0)) := by
  by_cases hx : ‖x‖ ≤ η
  · rw [if_neg (not_lt.2 hx)]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0:ℝ) < ε := hε
    unfold coefε
    rw [ramp_of_le hε' hx]; simp
  · push_neg at hx
    rw [if_pos hx]
    have := ((tendsto_ramp hx).const_mul (Γ' ‖x‖)).const_mul ‖x‖⁻¹
    simpa [coefε] using this


theorem abs_coefε_apply_le {Γ' : ℝ → ℝ} {η ε C : ℝ} (hη : 0 < η) (hε : 0 < ε)
    (hC : ∀ s, η ≤ s → |Γ' s| ≤ C) (x : Euc d) (L : Euc d →L[ℝ] ℝ) :
    |coefε Γ' η ε x * L x| ≤ C * ‖L‖ := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC η le_rfl)
  by_cases hx : ‖x‖ ≤ η
  · unfold coefε
    rw [ramp_of_le hε hx]
    simpa using mul_nonneg hC0 (norm_nonneg L)
  · push_neg at hx
    have hpos : 0 < ‖x‖ := by linarith
    unfold coefε
    have h1 := hC ‖x‖ hx.le
    have h3 := ramp_le_one η ε ‖x‖
    have h4 := ramp_nonneg η ε ‖x‖
    have h5 : |L x| ≤ ‖L‖ * ‖x‖ := by
      have := L.le_opNorm x
      simpa [Real.norm_eq_abs] using this
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg h4, abs_inv, abs_of_pos hpos]
    calc ‖x‖⁻¹ * (|Γ' ‖x‖| * ramp η ε ‖x‖) * |L x|
        ≤ ‖x‖⁻¹ * (C * 1) * (‖L‖ * ‖x‖) := by gcongr
      _ = C * ‖L‖ := by field_simp

theorem integrable_uε_mul {Γ Γ' : ℝ → ℝ} {η C : ℝ} (hη : 0 < η)
    (hc : ∀ r, 0 < r → ContinuousAt Γ' r) (hC : ∀ s, η ≤ s → |Γ' s| ≤ C) {ε : ℝ} (hε : 0 < ε)
    {f : Euc d → ℝ} (hf : Continuous f) (hint : Integrable (fun y => (1 + ‖y‖) * |f y|)) :
    Integrable (fun x => uε Γ Γ' η ε x * f x) := by
  have hcu : Continuous (uε Γ Γ' η ε : Euc d → ℝ) := continuous_uε hη hc hε
  have hB := abs_uε_le (d := d) (Γ := Γ) hη hε hc hC
  refine Integrable.mono' (hint.const_mul (|Γ η| + C)) (hcu.mul hf).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |uε Γ Γ' η ε x| * |f x| ≤ ((|Γ η| + C) * (1 + ‖x‖)) * |f x| :=
        mul_le_mul_of_nonneg_right (hB x) (abs_nonneg _)
    _ = _ := by ring

theorem integrable_coef_mul {Γ' : ℝ → ℝ} {η C : ℝ} (hη : 0 < η)
    (hc : ∀ r, 0 < r → ContinuousAt Γ' r) (hC : ∀ s, η ≤ s → |Γ' s| ≤ C) {ε : ℝ} (hε : 0 < ε)
    {φ : Euc d → ℝ} (hφ : TF φ) (i : Fin d) :
    Integrable (fun x => (coefε Γ' η ε x * x i) * fderiv ℝ φ x (ei i)) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC η le_rfl)
  have hcc : Continuous fun x : Euc d => coefε Γ' η ε x * x i :=
    (continuous_coefε hη hc hε).mul ((EuclideanSpace.proj i).continuous)
  refine Integrable.mono' (hφ.integrable_fderiv.const_mul C) ?_ (Eventually.of_forall fun x => ?_)
  · exact (hcc.mul (hφ.cont_g i)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_coefε_mul_le hη hε hC x i) (hφ.abs_g_le i x) (abs_nonneg _) hC0

theorem lap_eps {Γ Γ' : ℝ → ℝ} {η C : ℝ} (hη : 0 < η) (hc : ∀ r, 0 < r → ContinuousAt Γ' r)
    (hC : ∀ s, η ≤ s → |Γ' s| ≤ C) {ε : ℝ} (hε : 0 < ε) {φ : Euc d → ℝ} (hφ : TF φ) :
    ∫ x, uε Γ Γ' η ε x * lap φ x = -∫ x, coefε Γ' η ε x * fderiv ℝ φ x x := by
  have hlap : ∀ x, uε Γ Γ' η ε x * lap φ x = ∑ i, uε Γ Γ' η ε x * dd φ i x := fun x => by
    unfold lap; rw [Finset.mul_sum]
  have hlin : ∀ x, coefε Γ' η ε x * fderiv ℝ φ x x =
      ∑ i, (coefε Γ' η ε x * x i) * fderiv ℝ φ x (ei i) := fun x => by
    have h := congrArg (fderiv ℝ φ x) (sum_smul_ei x)
    rw [map_sum] at h
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul]; ring
  simp_rw [hlap, hlin]
  rw [integral_finset_sum _ (fun i _ => integrable_uε_mul hη hc hC hε (hφ.cont_dd i) (hφ.i2 i)),
    integral_finset_sum _ (fun i _ => integrable_coef_mul hη hc hC hε hφ i), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => ibp_eps hη hc hC hε hφ i

theorem ibp_lip {Γ Γ' : ℝ → ℝ} {η C : ℝ} (hη : 0 < η)
    (hΓ : ∀ r, 0 < r → HasDerivAt Γ (Γ' r) r) (hc : ∀ r, 0 < r → ContinuousAt Γ' r)
    (hC : ∀ s, η ≤ s → |Γ' s| ≤ C) {φ : Euc d → ℝ} (hφ : TF φ) :
    ∫ x, Γ (max ‖x‖ η) * lap φ x =
      -∫ x, (if η < ‖x‖ then ‖x‖⁻¹ * Γ' ‖x‖ else 0) * fderiv ℝ φ x x := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC η le_rfl)
  have hT1 : Tendsto (fun ε => ∫ x, uε Γ Γ' η ε x * lap φ x) (𝓝[>] 0)
      (𝓝 (∫ x, Γ (max ‖x‖ η) * lap φ x)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => (|Γ η| + C) * ∑ i, ((1 + ‖x‖) * |dd φ i x|)) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0:ℝ) < ε := hε
      exact ((continuous_uε hη hc hε').mul (continuous_finset_sum _ fun i _ => hφ.cont_dd i)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0:ℝ) < ε := hε
      refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := abs_uε_le (d := d) (Γ := Γ) hη hε' hc hC x
      have h2 : |lap φ x| ≤ ∑ i, |dd φ i x| := by
        unfold lap; exact Finset.abs_sum_le_sum_abs _ _
      calc |uε Γ Γ' η ε x| * |lap φ x| ≤ ((|Γ η| + C) * (1 + ‖x‖)) * ∑ i, |dd φ i x| :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = (|Γ η| + C) * ∑ i, ((1 + ‖x‖) * |dd φ i x|) := by rw [← Finset.mul_sum]; ring
    · exact (integrable_finset_sum _ fun i _ => hφ.i2 i).const_mul _
    · refine Eventually.of_forall fun x => ?_
      exact (tendsto_uε hη hΓ hc hC x).mul_const _
  have hT2 : Tendsto (fun ε => ∫ x, coefε Γ' η ε x * fderiv ℝ φ x x) (𝓝[>] 0)
      (𝓝 (∫ x, (if η < ‖x‖ then ‖x‖⁻¹ * Γ' ‖x‖ else 0) * fderiv ℝ φ x x)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => C * ‖fderiv ℝ φ x‖) ?_ ?_ ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0:ℝ) < ε := hε
      exact ((continuous_coefε hη hc hε').mul (hφ.cont_fderiv.clm_apply continuous_id)).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0:ℝ) < ε := hε
      refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs]
      exact abs_coefε_apply_le hη hε' hC x _
    · exact hφ.integrable_fderiv.const_mul _
    · refine Eventually.of_forall fun x => ?_
      exact (tendsto_coefε hη x).mul_const _
  have hT1' : Tendsto (fun ε => ∫ x, uε Γ Γ' η ε x * lap φ x) (𝓝[>] 0)
      (𝓝 (-∫ x, (if η < ‖x‖ then ‖x‖⁻¹ * Γ' ‖x‖ else 0) * fderiv ℝ φ x x)) := by
    refine (hT2.neg).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0:ℝ) < ε := hε
    exact (lap_eps hη hc hC hε' hφ).symm
  exact tendsto_nhds_unique hT1 hT1'


/-- spherical integral of `φ` over the sphere of radius `r`. -/
def Phi (φ : Euc d → ℝ) (r : ℝ) : ℝ := ∫ ω, φ (r • (ω : Euc d)) ∂(sphMeas d)

/-- spherical integral of the radial derivative. -/
def Phi' (φ : Euc d → ℝ) (r : ℝ) : ℝ := ∫ ω, fderiv ℝ φ (r • (ω : Euc d)) (ω : Euc d) ∂(sphMeas d)

theorem integrable_sphere {f : sphere (0 : Euc d) 1 → ℝ} (hf : Continuous f) :
    Integrable f (sphMeas d) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem hasDerivAt_Phi {φ : Euc d → ℝ} (hφ : TF φ) (r : ℝ) : HasDerivAt (Phi φ) (Phi' φ r) r := by
  obtain ⟨K, hK⟩ := hφ.bd
  have hdiff : Differentiable ℝ φ := hφ.c2.differentiable (by norm_num)
  have hF : ∀ r : ℝ, Continuous fun ω : sphere (0 : Euc d) 1 => φ (r • (ω : Euc d)) := fun r =>
    hφ.cont.comp (by fun_prop)
  have hF' : ∀ r : ℝ, Continuous fun ω : sphere (0 : Euc d) 1 => fderiv ℝ φ (r • (ω : Euc d)) (ω : Euc d) :=
    fun r => (hφ.cont_fderiv.comp (by fun_prop)).clm_apply
      continuous_subtype_val
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := sphMeas d)
    (F := fun (r : ℝ) (ω : sphere (0 : Euc d) 1) => φ (r • (ω : Euc d)))
    (F' := fun (r : ℝ) (ω : sphere (0 : Euc d) 1) => fderiv ℝ φ (r • (ω : Euc d)) (ω : Euc d))
    (x₀ := r) (bound := fun _ => K) (s := univ) univ_mem
    (Eventually.of_forall fun r => (hF r).aestronglyMeasurable)
    (integrable_sphere (hF r)) (hF' r).aestronglyMeasurable
    (Eventually.of_forall fun ω r' _ => by
      have h1 := (fderiv ℝ φ (r' • (ω : Euc d))).le_opNorm (ω : Euc d)
      have h2 : ‖(ω : Euc d)‖ = 1 := by simp
      rw [h2, mul_one] at h1
      exact h1.trans (hK _))
    (integrable_const K)
    (Eventually.of_forall fun ω r' _ => by
      have := (hdiff.differentiableAt (x := r' • (ω : Euc d))).hasFDerivAt.comp_hasDerivAt r'
        ((hasDerivAt_id r').smul_const (ω : Euc d))
      simpa [Function.comp_def] using this)
  exact this.2


theorem norm_smul_sph {r : ℝ} (hr : 0 ≤ r) (ω : sphere (0 : Euc d) 1) : ‖r • (ω : Euc d)‖ = r := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]
  simp

theorem polar_radial (hd : 1 ≤ d) {g : ℝ → ℝ} {φ : Euc d → ℝ}
    (hF : Integrable (fun x : Euc d => g ‖x‖ * φ x)) :
    ∫ x, g ‖x‖ * φ x = ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * (g r * Phi φ r) := by
  rw [polar_integral hd hF]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr' : (0:ℝ) < r := hr
  simp only [norm_smul_sph hr'.le]
  rw [integral_const_mul]
  rfl

theorem polar_radial_deriv (hd : 1 ≤ d) {g : ℝ → ℝ} {φ : Euc d → ℝ}
    (hF : Integrable (fun x : Euc d => g ‖x‖ * (‖x‖⁻¹ * fderiv ℝ φ x x))) :
    ∫ x, g ‖x‖ * (‖x‖⁻¹ * fderiv ℝ φ x x) = ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * (g r * Phi' φ r) := by
  rw [polar_integral hd hF]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr' : (0:ℝ) < r := hr
  simp only [norm_smul_sph hr'.le]
  rw [integral_const_mul]
  congr 2
  unfold Phi'
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [map_smul, smul_eq_mul]
  field_simp


theorem ibp_1d {q q' Φ Φ' : ℝ → ℝ} {η : ℝ} (hq : ∀ r, η < r → HasDerivAt q (q' r) r)
    (hΦ : ∀ r, HasDerivAt Φ (Φ' r) r)
    (i1 : IntegrableOn (fun r => q r * Φ' r) (Ioi η)) (i2 : IntegrableOn (fun r => q' r * Φ r) (Ioi η))
    (i3 : IntegrableOn (fun r => q r * Φ r) (Ioi η)) (hqc : ContinuousAt q η) :
    ∫ r in Ioi η, q r * Φ' r = -(q η * Φ η) - ∫ r in Ioi η, q' r * Φ r := by
  have hderiv : ∀ x ∈ Ioi η, HasDerivAt (fun y => q y * Φ y) (q' x * Φ x + q x * Φ' x) x :=
    fun x hx => (hq x hx).mul (hΦ x)
  have hint : IntegrableOn (fun x => q' x * Φ x + q x * Φ' x) (Ioi η) := i2.add i1
  have hzero : Tendsto (fun y => q y * Φ y) atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi hderiv hint i3
  have := integral_Ioi_mul_deriv_eq_deriv_mul (u := q) (v := Φ) (u' := q') (v' := Φ') (a := η)
    (a' := q η * Φ η) (b' := 0) hq (fun x _ => hΦ x) i1 i2 ?_ hzero
  · simpa using this
  · have h1 : ContinuousAt (fun y => q y * Φ y) η := hqc.mul (hΦ η).continuousAt
    exact h1.tendsto.mono_left nhdsWithin_le_nhds


theorem continuous_Phi {φ : Euc d → ℝ} (hφ : TF φ) : Continuous (Phi φ) :=
  continuous_iff_continuousAt.2 fun r => (hasDerivAt_Phi hφ r).continuousAt

theorem integrableOn_Phi' (hd : 1 ≤ d) {φ : Euc d → ℝ} (hφ : TF φ) :
    IntegrableOn (fun r : ℝ => r ^ (d - 1) * Phi' φ r) (Ioi 0) := by
  have hF : Integrable (fun x : Euc d => ‖x‖⁻¹ * fderiv ℝ φ x x) := by
    refine Integrable.mono' hφ.integrable_fderiv ?_ (Eventually.of_forall fun x => ?_)
    · exact (measurable_norm.inv.mul (hφ.cont_fderiv.clm_apply continuous_id).measurable).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_nonneg (norm_nonneg x)]
      by_cases hx : x = 0
      · subst hx; simp
      · have h5 : |fderiv ℝ φ x x| ≤ ‖fderiv ℝ φ x‖ * ‖x‖ := by
          have := (fderiv ℝ φ x).le_opNorm x
          simpa [Real.norm_eq_abs] using this
        have hp : 0 < ‖x‖ := norm_pos_iff.2 hx
        calc ‖x‖⁻¹ * |fderiv ℝ φ x x| ≤ ‖x‖⁻¹ * (‖fderiv ℝ φ x‖ * ‖x‖) := by gcongr
          _ = ‖fderiv ℝ φ x‖ := by field_simp
  have := polar_integrableOn hd hF
  refine this.congr_fun (fun r hr => ?_) measurableSet_Ioi
  have hr' : (0:ℝ) < r := hr
  simp only [norm_smul_sph hr'.le]
  unfold Phi'
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only [map_smul, smul_eq_mul]
  field_simp

theorem integrableOn_Phi (hd : 1 ≤ d) {φ : Euc d → ℝ} (hφ : TF φ) :
    IntegrableOn (fun r : ℝ => r ^ (d - 1) * ((1 + r) * |Phi φ r|)) (Ioi 0) := by
  have := polar_integrableOn hd hφ.i0
  have hm : Measurable fun r : ℝ => r ^ (d - 1) * ((1 + r) * |Phi φ r|) :=
    (measurable_id.pow_const _).mul ((measurable_const.add measurable_id).mul
      (continuous_Phi hφ).abs.measurable)
  refine Integrable.mono' this hm.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
  have hr' : (0:ℝ) < r := hr
  simp only [norm_smul_sph hr'.le]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [integral_const_mul]
  have h := norm_integral_le_integral_norm (μ := sphMeas d) (fun ω : sphere (0 : Euc d) 1 => φ (r • (ω : Euc d)))
  simp only [Real.norm_eq_abs] at h
  have h1 : 0 ≤ 1 + r := by linarith
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h h1) (by positivity)


theorem cont_of_q {Γ' : ℝ → ℝ} {n : ℕ} {q' : ℝ → ℝ}
    (hq : ∀ r, 0 < r → HasDerivAt (fun r => r ^ n * Γ' r) (q' r) r) (r : ℝ) (hr : 0 < r) :
    ContinuousAt Γ' r := by
  have h1 : ContinuousAt (fun s => s ^ n * Γ' s) r := (hq r hr).continuousAt
  have h2 : ContinuousAt (fun s : ℝ => s ^ n) r := (continuous_pow n).continuousAt
  have h3 := h1.div h2 (pow_ne_zero _ hr.ne')
  refine h3.congr ?_
  filter_upwards [Ioi_mem_nhds hr] with s hs
  have : s ^ n ≠ 0 := pow_ne_zero _ (ne_of_gt hs)
  simp only [Pi.div_apply]
  field_simp

theorem abs_Γ_sub_le {Γ Γ' : ℝ → ℝ} {η C : ℝ} (hη : 0 < η)
    (hΓ : ∀ r, 0 < r → HasDerivAt Γ (Γ' r) r) (hc : ∀ r, 0 < r → ContinuousAt Γ' r)
    (hC : ∀ s, η ≤ s → |Γ' s| ≤ C) {r : ℝ} (hr : η ≤ r) : |Γ r - Γ η| ≤ C * (r - η) := by
  have hcont : ContinuousOn Γ' (Icc η r) := fun s hs =>
    (hc s (lt_of_lt_of_le hη hs.1)).continuousWithinAt
  have hft : ∫ s in η..r, Γ' s = Γ r - Γ η := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => ?_) (hcont.mono (by
      rw [Set.uIcc_of_le hr]) |>.intervalIntegrable)
    rw [Set.uIcc_of_le hr] at hs
    exact hΓ s (lt_of_lt_of_le hη hs.1)
  rw [← hft]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := η) (b := r) (C := C) (f := Γ')
    (fun s hs => by
      rw [Set.uIoc_of_le hr] at hs
      simpa [Real.norm_eq_abs] using hC s hs.1.le)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ r - η)] at this
  exact this

theorem continuous_Γmax {Γ Γ' : ℝ → ℝ} {η : ℝ} (hη : 0 < η)
    (hΓ : ∀ r, 0 < r → HasDerivAt Γ (Γ' r) r) :
    Continuous fun x : Euc d => Γ (max ‖x‖ η) := by
  have : ContinuousOn Γ (Ioi 0) := fun r hr => (hΓ r hr).continuousAt.continuousWithinAt
  refine this.comp_continuous (continuous_norm.max continuous_const) fun x => ?_
  exact lt_of_lt_of_le hη (le_max_right _ _)

theorem abs_Γmax_le {Γ Γ' : ℝ → ℝ} {η C : ℝ} (hη : 0 < η)
    (hΓ : ∀ r, 0 < r → HasDerivAt Γ (Γ' r) r) (hc : ∀ r, 0 < r → ContinuousAt Γ' r)
    (hC : ∀ s, η ≤ s → |Γ' s| ≤ C) (x : Euc d) :
    |Γ (max ‖x‖ η)| ≤ (|Γ η| + C) * (1 + ‖x‖) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC η le_rfl)
  have h := abs_Γ_sub_le hη hΓ hc hC (le_max_right ‖x‖ η)
  have hm : max ‖x‖ η - η ≤ ‖x‖ := by
    rcases le_total ‖x‖ η with h1 | h1
    · rw [max_eq_right h1]; simp [norm_nonneg]
    · rw [max_eq_left h1]; linarith
  have h2 : max ‖x‖ η - η ≥ 0 := by linarith [le_max_right ‖x‖ η]
  calc |Γ (max ‖x‖ η)| ≤ |Γ η| + |Γ (max ‖x‖ η) - Γ η| := by
        have := abs_add_le (Γ η) (Γ (max ‖x‖ η) - Γ η); simpa using this
    _ ≤ |Γ η| + C * ‖x‖ := by nlinarith
    _ ≤ _ := by nlinarith [norm_nonneg x, abs_nonneg (Γ η)]


theorem abs_radD_le (φ : Euc d → ℝ) (x : Euc d) (h : TF φ) :
    |‖x‖⁻¹ * fderiv ℝ φ x x| ≤ ‖fderiv ℝ φ x‖ := by
  rw [abs_mul, abs_inv, abs_of_nonneg (norm_nonneg x)]
  by_cases hx : x = 0
  · subst hx; simp
  · have h5 : |fderiv ℝ φ x x| ≤ ‖fderiv ℝ φ x‖ * ‖x‖ := by
      have := (fderiv ℝ φ x).le_opNorm x
      simpa [Real.norm_eq_abs] using this
    have hp : 0 < ‖x‖ := norm_pos_iff.2 hx
    calc ‖x‖⁻¹ * |fderiv ℝ φ x x| ≤ ‖x‖⁻¹ * (‖fderiv ℝ φ x‖ * ‖x‖) := by gcongr
      _ = ‖fderiv ℝ φ x‖ := by field_simp

theorem abs_Γ_le_r {Γ Γ' : ℝ → ℝ} {η C : ℝ} (hη : 0 < η)
    (hΓ : ∀ r, 0 < r → HasDerivAt Γ (Γ' r) r) (hc : ∀ r, 0 < r → ContinuousAt Γ' r)
    (hC : ∀ s, η ≤ s → |Γ' s| ≤ C) {r : ℝ} (hr : η ≤ r) :
    |Γ r| ≤ (|Γ η| + C) * (1 + r) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC η le_rfl)
  have h := abs_Γ_sub_le hη hΓ hc hC hr
  calc |Γ r| ≤ |Γ η| + |Γ r - Γ η| := by
        have := abs_add_le (Γ η) (Γ r - Γ η); simpa using this
    _ ≤ |Γ η| + C * r := by nlinarith
    _ ≤ _ := by nlinarith [abs_nonneg (Γ η)]


theorem measurable_Phi' {φ : Euc d → ℝ} (hφ : TF φ) : Measurable (Phi' φ) := by
  have : Phi' φ = deriv (Phi φ) := funext fun r => (hasDerivAt_Phi hφ r).deriv.symm
  rw [this]; exact measurable_deriv _

theorem core_1d (hd : 1 ≤ d) {Γ Γ' : ℝ → ℝ} {η C l : ℝ} (hη : 0 < η)
    (hΓ : ∀ r, 0 < r → HasDerivAt Γ (Γ' r) r) (hΓ'm : Measurable Γ')
    (hq : ∀ r, 0 < r → HasDerivAt (fun r => r ^ (d - 1) * Γ' r) (l * r ^ (d - 1) * Γ r) r)
    (hC : ∀ s, η ≤ s → |Γ' s| ≤ C) {φ : Euc d → ℝ} (hφ : TF φ) :
    ∫ r in Ioi η, r ^ (d - 1) * Γ' r * Phi' φ r =
      -(η ^ (d - 1) * Γ' η * Phi φ η) - l * ∫ r in Ioi η, r ^ (d - 1) * (Γ r * Phi φ r) := by
  have hc := cont_of_q hq
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC η le_rfl)
  have hsub : Ioi η ⊆ Ioi (0:ℝ) := Ioi_subset_Ioi hη.le
  have hP' := (integrableOn_Phi' hd hφ).mono_set hsub
  have hP := (integrableOn_Phi hd hφ).mono_set hsub
  have hqcont : ContinuousOn (fun r : ℝ => r ^ (d - 1) * Γ' r) (Ioi η) :=
    fun r hr => (hq r (lt_trans hη hr)).continuousAt.continuousWithinAt
  have hΓcont : ContinuousOn Γ (Ioi η) :=
    fun r hr => (hΓ r (lt_trans hη hr)).continuousAt.continuousWithinAt
  have hPhi := continuous_Phi hφ
  have i1 : IntegrableOn (fun r => (r ^ (d - 1) * Γ' r) * Phi' φ r) (Ioi η) := by
    refine Integrable.mono' (hP'.norm.const_mul C) ?_ ?_
    · have : Measurable fun r : ℝ => (r ^ (d - 1) * Γ' r) * Phi' φ r :=
        ((measurable_id.pow_const _).mul hΓ'm).mul (measurable_Phi' hφ)
      exact this.aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
      have hr' : η < r := hr
      rw [Real.norm_eq_abs, show (r ^ (d - 1) * Γ' r) * Phi' φ r = Γ' r * (r ^ (d - 1) * Phi' φ r) by ring,
        abs_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hC r hr'.le) (abs_nonneg _)
  have i3 : IntegrableOn (fun r => (r ^ (d - 1) * Γ' r) * Phi φ r) (Ioi η) := by
    refine Integrable.mono' (hP.const_mul C) ?_ ?_
    · exact (hqcont.mul hPhi.continuousOn).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
      have hr' : η < r := hr
      have hr0 : 0 < r := lt_trans hη hr'
      rw [Real.norm_eq_abs, show (r ^ (d - 1) * Γ' r) * Phi φ r = Γ' r * (r ^ (d - 1) * Phi φ r) by ring,
        abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hr0.le _)]
      have h1 : 1 ≤ 1 + r := by linarith
      calc |Γ' r| * (r ^ (d - 1) * |Phi φ r|) ≤ C * (r ^ (d - 1) * |Phi φ r|) :=
            mul_le_mul_of_nonneg_right (hC r hr'.le) (by positivity)
        _ ≤ C * (r ^ (d - 1) * ((1 + r) * |Phi φ r|)) := by
            gcongr
            nlinarith [abs_nonneg (Phi φ r)]
  have i2 : IntegrableOn (fun r => (l * r ^ (d - 1) * Γ r) * Phi φ r) (Ioi η) := by
    refine Integrable.mono' (hP.const_mul (|l| * (|Γ η| + C))) ?_ ?_
    · exact (((continuousOn_const.mul (continuous_pow _).continuousOn).mul hΓcont).mul
        hPhi.continuousOn).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
      have hr' : η < r := hr
      have hr0 : 0 < r := lt_trans hη hr'
      have hG := abs_Γ_le_r hη hΓ hc hC hr'.le
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hr0.le _)]
      calc |l| * r ^ (d - 1) * |Γ r| * |Phi φ r|
          ≤ |l| * r ^ (d - 1) * ((|Γ η| + C) * (1 + r)) * |Phi φ r| := by gcongr
        _ = |l| * (|Γ η| + C) * (r ^ (d - 1) * ((1 + r) * |Phi φ r|)) := by ring
  have key := ibp_1d (q := fun r => r ^ (d - 1) * Γ' r) (q' := fun r => l * r ^ (d - 1) * Γ r)
    (Φ := Phi φ) (Φ' := Phi' φ) (η := η) (fun r hr => hq r (lt_trans hη hr))
    (hasDerivAt_Phi hφ) i1 i2 i3 (hq η hη).continuousAt
  rw [key]
  congr 1
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  ring

theorem core_weak (hd : 1 ≤ d) {Γ Γ' : ℝ → ℝ} {η C l : ℝ} (hη : 0 < η)
    (hΓ : ∀ r, 0 < r → HasDerivAt Γ (Γ' r) r) (hΓ'm : Measurable Γ')
    (hq : ∀ r, 0 < r → HasDerivAt (fun r => r ^ (d - 1) * Γ' r) (l * r ^ (d - 1) * Γ r) r)
    (hC : ∀ s, η ≤ s → |Γ' s| ≤ C) {φ : Euc d → ℝ} (hφ : TF φ) :
    ∫ x, Γ (max ‖x‖ η) * (l * φ x - lap φ x) =
      l * Γ η * (∫ x in closedBall (0 : Euc d) η, φ x) - η ^ (d - 1) * Γ' η * Phi φ η := by
  have hc := cont_of_q hq
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC η le_rfl)
  have hcu := continuous_Γmax (d := d) hη hΓ
  have hu_int : Integrable (fun x : Euc d => Γ (max ‖x‖ η) * φ x) := by
    refine Integrable.mono' (hφ.i0.const_mul (|Γ η| + C)) (hcu.mul hφ.cont).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |Γ (max ‖x‖ η)| * |φ x| ≤ ((|Γ η| + C) * (1 + ‖x‖)) * |φ x| :=
          mul_le_mul_of_nonneg_right (abs_Γmax_le hη hΓ hc hC x) (abs_nonneg _)
      _ = _ := by ring
  have hul_int : Integrable (fun x : Euc d => Γ (max ‖x‖ η) * lap φ x) := by
    have hb : Integrable (fun x : Euc d => (|Γ η| + C) * ∑ i, ((1 + ‖x‖) * |dd φ i x|)) :=
      (integrable_finset_sum _ fun i _ => hφ.i2 i).const_mul _
    refine Integrable.mono' hb
      (hcu.mul (continuous_finset_sum _ fun i _ => hφ.cont_dd i)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h2 : |lap φ x| ≤ ∑ i, |dd φ i x| := by
      unfold lap; exact Finset.abs_sum_le_sum_abs _ _
    calc |Γ (max ‖x‖ η)| * |lap φ x| ≤ ((|Γ η| + C) * (1 + ‖x‖)) * ∑ i, |dd φ i x| :=
          mul_le_mul (abs_Γmax_le hη hΓ hc hC x) h2 (abs_nonneg _) (by positivity)
      _ = (|Γ η| + C) * ∑ i, ((1 + ‖x‖) * |dd φ i x|) := by rw [← Finset.mul_sum]; ring
  -- step 1: reduce to the first-order integral
  have h1 : ∫ x, Γ (max ‖x‖ η) * (l * φ x - lap φ x) =
      l * (∫ x, Γ (max ‖x‖ η) * φ x) + ∫ x, (if η < ‖x‖ then ‖x‖⁻¹ * Γ' ‖x‖ else 0) * fderiv ℝ φ x x := by
    have e : ∀ x : Euc d, Γ (max ‖x‖ η) * (l * φ x - lap φ x) =
        l * (Γ (max ‖x‖ η) * φ x) - Γ (max ‖x‖ η) * lap φ x := fun x => by ring
    simp_rw [e]
    have e2 := ibp_lip hη hΓ hc hC hφ
    rw [integral_sub (hu_int.const_mul l) hul_int, e2]
    simp only [integral_const_mul]
    ring
  rw [h1]
  have hsub : Ioi η ⊆ Ioi (0:ℝ) := Ioi_subset_Ioi hη.le
  -- the ball part
  have hB : ∫ x in closedBall (0 : Euc d) η, φ x = ∫ r in Ioc 0 η, r ^ (d - 1) * Phi φ r := by
    rw [← integral_indicator measurableSet_closedBall]
    have e : ∀ x : Euc d, (closedBall (0 : Euc d) η).indicator φ x =
        (Iic η).indicator (fun _ => (1:ℝ)) ‖x‖ * φ x := fun x => by
      by_cases hx : ‖x‖ ≤ η
      · rw [indicator_of_mem (by simpa using hx), indicator_of_mem (show ‖x‖ ∈ Iic η from hx), one_mul]
      · rw [indicator_of_notMem (by simpa using hx), indicator_of_notMem (show ‖x‖ ∉ Iic η from hx),
          zero_mul]
    simp_rw [e]
    rw [polar_radial hd (g := (Iic η).indicator (fun _ => (1:ℝ))) (by
      simp_rw [← e]; exact hφ.integrable_phi.indicator measurableSet_closedBall)]
    have e2 : ∀ r : ℝ, r ^ (d - 1) * ((Iic η).indicator (fun _ => (1:ℝ)) r * Phi φ r) =
        (Iic η).indicator (fun r => r ^ (d - 1) * Phi φ r) r := fun r => by
      by_cases hr : r ≤ η
      · rw [indicator_of_mem (show r ∈ Iic η from hr), indicator_of_mem (show r ∈ Iic η from hr), one_mul]
      · rw [indicator_of_notMem (show r ∉ Iic η from hr), indicator_of_notMem (show r ∉ Iic η from hr)]
        simp
    simp_rw [e2]
    rw [setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic]
  -- the radial part
  have hUint : IntegrableOn (fun r => r ^ (d - 1) * (Γ (max r η) * Phi φ r)) (Ioi 0) := by
    have := polar_integrableOn hd hu_int
    refine this.congr_fun (fun r hr => ?_) measurableSet_Ioi
    have hr' : (0:ℝ) < r := hr
    simp only [norm_smul_sph hr'.le]
    rw [integral_const_mul]
    rfl
  have hU : ∫ x, Γ (max ‖x‖ η) * φ x =
      Γ η * (∫ r in Ioc 0 η, r ^ (d - 1) * Phi φ r) +
        ∫ r in Ioi η, r ^ (d - 1) * (Γ r * Phi φ r) := by
    rw [polar_radial hd (g := fun t => Γ (max t η)) hu_int]
    have hI1 := hUint.mono_set (Ioc_subset_Ioi_self : Ioc (0:ℝ) η ⊆ Ioi 0)
    have hI2 := hUint.mono_set hsub
    rw [← Ioc_union_Ioi_eq_Ioi hη.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hI1 hI2]
    have e1 : ∀ r ∈ Ioc (0:ℝ) η, r ^ (d - 1) * (Γ (max r η) * Phi φ r) =
        Γ η * (r ^ (d - 1) * Phi φ r) := fun r hr => by rw [max_eq_right hr.2]; ring
    have e2 : ∀ r ∈ Ioi η, r ^ (d - 1) * (Γ (max r η) * Phi φ r) =
        r ^ (d - 1) * (Γ r * Phi φ r) := fun r hr => by rw [max_eq_left (le_of_lt hr)]
    rw [setIntegral_congr_fun measurableSet_Ioc e1, integral_const_mul,
      setIntegral_congr_fun measurableSet_Ioi e2]
    done
  -- the derivative part
  have hD : ∫ x : Euc d, (if η < ‖x‖ then ‖x‖⁻¹ * Γ' ‖x‖ else 0) * fderiv ℝ φ x x =
      ∫ r in Ioi η, r ^ (d - 1) * Γ' r * Phi' φ r := by
    have e : ∀ x : Euc d, (if η < ‖x‖ then ‖x‖⁻¹ * Γ' ‖x‖ else 0) * fderiv ℝ φ x x =
        (fun t => if η < t then Γ' t else 0) ‖x‖ * (‖x‖⁻¹ * fderiv ℝ φ x x) := fun x => by
      by_cases hx : η < ‖x‖
      · simp only [if_pos hx]; ring
      · simp only [if_neg hx]; ring
    have hgm : Measurable fun t : ℝ => if η < t then Γ' t else 0 :=
      Measurable.ite (measurableSet_lt measurable_const measurable_id) hΓ'm measurable_const
    have hF : Integrable (fun x : Euc d => (fun t : ℝ => if η < t then Γ' t else 0) ‖x‖ *
        (‖x‖⁻¹ * fderiv ℝ φ x x)) := by
      refine Integrable.mono' (hφ.integrable_fderiv.const_mul C) ?_ (Eventually.of_forall fun x => ?_)
      · exact ((hgm.comp measurable_norm).mul (measurable_norm.inv.mul
          (hφ.cont_fderiv.clm_apply continuous_id).measurable)).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul]
        have h1 : |(fun t : ℝ => if η < t then Γ' t else 0) ‖x‖| ≤ C := by
          by_cases hx : η < ‖x‖
          · simp only [if_pos hx]; exact hC _ hx.le
          · simp only [if_neg hx]; simpa using hC0
        exact mul_le_mul h1 (abs_radD_le φ x hφ) (abs_nonneg _) hC0
    refine (integral_congr_ae (Eventually.of_forall e)).trans
      ((polar_radial_deriv hd (g := fun t : ℝ => if η < t then Γ' t else 0) (φ := φ) hF).trans ?_)
    have e2 : ∀ r : ℝ, r ^ (d - 1) * ((fun t : ℝ => if η < t then Γ' t else 0) r * Phi' φ r) =
        (Ioi η).indicator (fun r => r ^ (d - 1) * Γ' r * Phi' φ r) r := fun r => by
      by_cases hr : η < r
      · rw [indicator_of_mem (show r ∈ Ioi η from hr)]; simp only [if_pos hr]; ring
      · rw [indicator_of_notMem (show r ∉ Ioi η from hr)]; simp only [if_neg hr]; ring
    simp_rw [e2]
    rw [setIntegral_indicator measurableSet_Ioi, Ioi_inter_Ioi, max_eq_right hη.le]
  rw [hD, core_1d hd hη hΓ hΓ'm hq hC hφ, hU, hB]
  ring

end HRS.Commutator.SmearAux
