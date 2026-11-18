import HRS.MS.SpecAux85

/-!
# S8M: dilation of the log-Sobolev inequality (S8.7, R1)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_lsi_dilate`: a probability density `ρ` with
`c₁ r^n gd(r·) ≤ ρ ≤ c₂ r^n gd(r·)` (`n = dim V`, `r > 0`; the Gaussian of precision `r²`) satisfies
`s8p_LSI (ρ dx) (2 c₂ / (c₁ r²))`.  (Rescaling `ρ̃(y) = r^{-n} ρ(y/r)` reduces to the standard Gaussian,
`s8p_lsi_of_comparable`.)
-/

noncomputable section

open MeasureTheory Real

namespace HRS.MS.Spec

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem s8p_dil_integral {r : ℝ} (hr : 0 < r) (f : V → ℝ) :
    ∫ x, f (r • x) = (r ^ Module.finrank ℝ V)⁻¹ * ∫ x, f x := by
  rw [MeasureTheory.Measure.integral_comp_smul volume f r, smul_eq_mul, abs_of_pos (by positivity)]

theorem s8p_dil_withDensity {ρ : V → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (h : V → ℝ) :
    ∫ x, h x ∂(volume.withDensity (fun x => ENNReal.ofReal (ρ x))) = ∫ x, ρ x * h x := by
  rw [integral_withDensity_eq_integral_toReal_smul (hρm.ennreal_ofReal)
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [ENNReal.toReal_ofReal (hρ0 x)]

theorem s8p_dil_integrable {ρ : V → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (h : V → ℝ) :
    Integrable h (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) ↔ Integrable (fun x => ρ x * h x) := by
  rw [integrable_withDensity_iff_integrable_smul' (hρm.ennreal_ofReal)
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  refine integrable_congr (ae_of_all _ fun x => ?_)
  simp [ENNReal.toReal_ofReal (hρ0 x)]

/-- Transport between the measure with density `r^{-n} ρ(y/r)` and the measure with density `ρ`. -/
theorem s8p_dil_transport {ρ : V → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {r : ℝ} (hr : 0 < r)
    (h : V → ℝ) :
    ∫ y, h y ∂(volume.withDensity (fun y => ENNReal.ofReal ((r ^ Module.finrank ℝ V)⁻¹ * ρ (r⁻¹ • y)))) =
      ∫ x, h (r • x) ∂(volume.withDensity (fun x => ENNReal.ofReal (ρ x))) := by
  set n := Module.finrank ℝ V with hn
  have hrn : 0 < r ^ n := by positivity
  have hm : Measurable (fun y : V => (r ^ n)⁻¹ * ρ (r⁻¹ • y)) :=
    measurable_const.mul (hρm.comp (measurable_const_smul _))
  rw [s8p_dil_withDensity hm (fun y => by have := hρ0 (r⁻¹ • y); positivity),
    s8p_dil_withDensity hρm hρ0]
  have := s8p_dil_integral (V := V) hr (fun y => (r ^ n)⁻¹ * ρ (r⁻¹ • y) * h y)
  simp only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] at this
  rw [← hn] at this
  rw [show (∫ x, ρ x * h (r • x)) = ∫ x, r ^ n * ((r ^ n)⁻¹ * ρ x * h (r • x)) by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    field_simp]
  rw [integral_const_mul, this]
  field_simp

theorem s8p_dil_transport_int {ρ : V → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {r : ℝ} (hr : 0 < r)
    (h : V → ℝ) :
    Integrable h (volume.withDensity (fun y => ENNReal.ofReal ((r ^ Module.finrank ℝ V)⁻¹ * ρ (r⁻¹ • y)))) ↔
      Integrable (fun x => h (r • x)) (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) := by
  set n := Module.finrank ℝ V with hn
  have hrn : 0 < r ^ n := by positivity
  have hm : Measurable (fun y : V => (r ^ n)⁻¹ * ρ (r⁻¹ • y)) :=
    measurable_const.mul (hρm.comp (measurable_const_smul _))
  rw [s8p_dil_integrable hm (fun y => by have := hρ0 (r⁻¹ • y); positivity),
    s8p_dil_integrable hρm hρ0, ← integrable_comp_smul_iff volume
      (fun y => (r ^ n)⁻¹ * ρ (r⁻¹ • y) * h y) hr.ne']
  have e : (fun x : V => (r ^ n)⁻¹ * ρ (r⁻¹ • r • x) * h (r • x)) =
      fun x => (r ^ n)⁻¹ * (ρ x * h (r • x)) := by
    funext x; simp only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]; ring
  rw [e]
  exact integrable_const_mul_iff (isUnit_iff_ne_zero.2 (inv_ne_zero hrn.ne')) _

theorem s8p_lsi_dilate {ρ : V → ℝ} (hρm : Measurable ρ) {r c1 c2 : ℝ} (hr : 0 < r) (hc1 : 0 < c1)
    (hlo : ∀ x, c1 * (r ^ Module.finrank ℝ V * s8p_gd (r • x)) ≤ ρ x)
    (hhi : ∀ x, ρ x ≤ c2 * (r ^ Module.finrank ℝ V * s8p_gd (r • x)))
    (hone : ∫ x, ρ x = 1) :
    s8p_LSI (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) (2 * c2 / c1 / r ^ 2) := by
  set n := Module.finrank ℝ V with hn
  have hrn : 0 < r ^ n := by positivity
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x =>
    (mul_nonneg hc1.le (mul_nonneg hrn.le (s8p_gd_pos _).le)).trans (hlo x)
  set ρ' : V → ℝ := fun y => (r ^ n)⁻¹ * ρ (r⁻¹ • y) with hρ'
  have hρ'm : Measurable ρ' := measurable_const.mul (hρm.comp (measurable_const_smul _))
  have hlo' : ∀ y, c1 * s8p_gd y ≤ ρ' y := fun y => by
    have := hlo (r⁻¹ • y)
    simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] at this
    simp only [hρ']
    rw [le_inv_mul_iff₀ hrn]
    linarith
  have hhi' : ∀ y, ρ' y ≤ c2 * s8p_gd y := fun y => by
    have := hhi (r⁻¹ • y)
    simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] at this
    simp only [hρ']
    rw [inv_mul_le_iff₀ hrn]
    linarith
  have hone' : ∫ y, ρ' y = 1 := by
    have := s8p_dil_integral (V := V) hr ρ'
    simp only [hρ', smul_smul, inv_mul_cancel₀ hr.ne', one_smul] at this
    have h2 : ∫ x, (r ^ n)⁻¹ * ρ x = (r ^ n)⁻¹ * 1 := by rw [integral_const_mul, hone]
    simp only [hρ'] at this ⊢
    rw [h2] at this
    have h3 : (r ^ n)⁻¹ * 1 = (r ^ n)⁻¹ * ∫ y, (r ^ n)⁻¹ * ρ (r⁻¹ • y) := this
    have := mul_left_cancel₀ (inv_ne_zero hrn.ne') h3
    exact this.symm
  have hL := s8p_lsi_of_comparable hρ'm hc1 hlo' hhi' hone'
  intro u hu hmem hint
  set ut : V → ℝ := fun y => u (r⁻¹ • y) with hut
  have hutc : ContDiff ℝ 2 ut := hu.comp (contDiff_const_smul _)
  have hutr : ∀ x, ut (r • x) = u x := fun x => by
    simp only [hut, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have hfd : ∀ y, ‖fderiv ℝ ut y‖ = r⁻¹ * ‖fderiv ℝ u (r⁻¹ • y)‖ := fun y => by
    have h1 : HasFDerivAt ut ((fderiv ℝ u (r⁻¹ • y)).comp (r⁻¹ • ContinuousLinearMap.id ℝ V)) y := by
      have h2 : HasFDerivAt (fun y : V => r⁻¹ • y) (r⁻¹ • ContinuousLinearMap.id ℝ V) y :=
        (hasFDerivAt_id y).const_smul r⁻¹
      exact (hu.differentiable (by norm_num) _).hasFDerivAt.comp y h2
    rw [h1.fderiv]
    have : (fderiv ℝ u (r⁻¹ • y)).comp (r⁻¹ • ContinuousLinearMap.id ℝ V) = r⁻¹ • fderiv ℝ u (r⁻¹ • y) := by
      ext v; simp
    rw [this, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le)]
  have hfdr : ∀ x, ‖fderiv ℝ ut (r • x)‖ ^ 2 = r⁻¹ ^ 2 * ‖fderiv ℝ u x‖ ^ 2 := fun x => by
    rw [hfd]; simp only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]; rw [mul_pow]
  set μ := volume.withDensity (fun x => ENNReal.ofReal (ρ x)) with hμ
  have hint2 : Integrable (fun y => ut y ^ 2) (volume.withDensity (fun y => ENNReal.ofReal (ρ' y))) := by
    rw [s8p_dil_transport_int hρm hρ0 hr]
    simp only [hutr]
    exact (memLp_two_iff_integrable_sq hmem.aestronglyMeasurable).1 hmem
  have hmem' : MemLp ut 2 (volume.withDensity (fun y => ENNReal.ofReal (ρ' y))) :=
    (memLp_two_iff_integrable_sq hutc.continuous.aestronglyMeasurable).2 hint2
  have hint' : Integrable (fun y => ‖fderiv ℝ ut y‖ ^ 2)
      (volume.withDensity (fun y => ENNReal.ofReal (ρ' y))) := by
    rw [s8p_dil_transport_int hρm hρ0 hr]
    simp only [hfdr]
    exact hint.const_mul _
  obtain ⟨hI, hle⟩ := hL ut hutc hmem' hint'
  have T : ∀ (F : ℝ → ℝ), (∫ y, F (ut y) ∂(volume.withDensity (fun y => ENNReal.ofReal (ρ' y)))) =
      ∫ x, F (u x) ∂μ := fun F => by
    rw [s8p_dil_transport hρm hρ0 hr]
    simp only [hutr]
    rfl
  refine ⟨?_, ?_⟩
  · have := (s8p_dil_transport_int hρm hρ0 hr (fun y => ut y ^ 2 * Real.log (ut y ^ 2))).1 hI
    simpa only [hutr] using this
  · have h1 := T (fun t => t ^ 2 * Real.log (t ^ 2))
    have h2 := T (fun t => t ^ 2)
    rw [h1, h2] at hle
    have h3 : ∫ y, ‖fderiv ℝ ut y‖ ^ 2 ∂(volume.withDensity (fun y => ENNReal.ofReal (ρ' y))) =
        r⁻¹ ^ 2 * ∫ x, ‖fderiv ℝ u x‖ ^ 2 ∂μ := by
      rw [s8p_dil_transport hρm hρ0 hr]
      simp only [hfdr]
      exact integral_const_mul _ _
    rw [h3] at hle
    calc _ ≤ 2 * c2 / c1 * (r⁻¹ ^ 2 * ∫ x, ‖fderiv ℝ u x‖ ^ 2 ∂μ) := hle
      _ = _ := by field_simp

end HRS.MS.Spec
