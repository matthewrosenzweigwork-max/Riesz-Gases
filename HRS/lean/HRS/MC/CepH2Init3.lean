import HRS.MC.CepH2Init2

/-!
# CEPH2, C4 (c): the mollified free energy is below the entropy up to a small error
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

theorem h2_integral_dMeas {ρ : Ch N → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (f : Ch N → ℝ) :
    ∫ y, f y ∂(h2_dMeas ρ) = ∫ x in cep_cell N, ρ x * f x := by
  unfold h2_dMeas
  rw [integral_withDensity_eq_integral_toReal_smul (f := fun x => ENNReal.ofReal (ρ x))
    (ENNReal.measurable_ofReal.comp hρ) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hρ0 y)]

theorem h2_integrable_dMeas_iff {ρ : Ch N → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (f : Ch N → ℝ) :
    Integrable f (h2_dMeas ρ) ↔ Integrable (fun x => ρ x * f x) (volume.restrict (cep_cell N)) := by
  unfold h2_dMeas
  rw [integrable_withDensity_iff_integrable_smul' (f := fun x => ENNReal.ofReal (ρ x))
    (ENNReal.measurable_ofReal.comp hρ) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integrable_congr (ae_of_all _ fun y => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hρ0 y)]

theorem h2_density_Uint {U : Ch N → ℝ} (hU : Continuous U)
    (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ U z)
    {θ : ℝ} (hθ : 0 < θ) {ρ : Ch N → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫⁻ x in cep_cell N, ENNReal.ofReal (ρ x) = 1)
    (hΦ : Integrable (fun x => ρ x * Real.log (ρ x) + ρ x * U x / θ) (volume.restrict (cep_cell N)))
    (hmom : Integrable (fun y => ‖h2_perp y‖ ^ 2) (h2_dMeas ρ)) :
    Integrable (fun x => ρ x * U x) (volume.restrict (cep_cell N)) ∧
      Integrable (fun x => ρ x * Real.log (ρ x)) (volume.restrict (cep_cell N)) := by
  obtain ⟨c, C, hc, hQ⟩ := h2_U_lower hconf
  have hρi := h2_integrable_of_lintegral hρ hρ0 hρ1
  have hρr : Integrable (fun x => ρ x * ‖h2_perp x‖ ^ 2) (volume.restrict (cep_cell N)) :=
    (h2_integrable_dMeas_iff hρ hρ0 _).1 hmom
  set a : ℝ := c / θ with ha
  have ha0 : 0 < a := by positivity
  have hgauss : Integrable (fun x : Ch N => Real.exp (-a * ‖h2_perp x‖ ^ 2)) (volume.restrict (cep_cell N)) := by
    refine ⟨(Real.continuous_exp.comp (continuous_const.mul (h2_continuous_perp.norm.pow 2))).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => (Real.exp_pos _).le)]
    exact h2_lintegral_cell_gauss ha0
  set w : Ch N → ℝ := fun x => Real.exp (C / θ) * Real.exp (-a * ‖h2_perp x‖ ^ 2) with hw
  have hwi : Integrable w (volume.restrict (cep_cell N)) := hgauss.const_mul _
  have hwpos : ∀ x, 0 < w x := fun x => mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have hlogw : ∀ x, Real.log (w x) = C / θ - a * ‖h2_perp x‖ ^ 2 := fun x => by
    simp only [hw]
    rw [Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]; ring
  have hmeasρU : Measurable fun x => ρ x * (U x - (c * ‖h2_perp x‖ ^ 2 - C)) / θ :=
    ((hρ.mul (hU.measurable.sub ((continuous_const.mul (h2_continuous_perp.norm.pow 2)).sub continuous_const).measurable)).div_const θ)
  have hbd : Integrable (fun x => ρ x * Real.log (ρ x) + ρ x * U x / θ + w x) (volume.restrict (cep_cell N)) :=
    hΦ.add hwi
  have hI : Integrable (fun x => ρ x * (U x - (c * ‖h2_perp x‖ ^ 2 - C)) / θ) (volume.restrict (cep_cell N)) := by
    refine Integrable.mono' hbd hmeasρU.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    have h0 : 0 ≤ ρ x * (U x - (c * ‖h2_perp x‖ ^ 2 - C)) / θ :=
      div_nonneg (mul_nonneg (hρ0 x) (by linarith [hQ x])) hθ.le
    rw [Real.norm_of_nonneg h0]
    have ht := h2_tangent (hρ0 x) (hwpos x)
    rw [hlogw x] at ht
    have e : ρ x * (U x - (c * ‖h2_perp x‖ ^ 2 - C)) / θ =
        (ρ x * Real.log (ρ x) + ρ x * U x / θ) - (ρ x * Real.log (ρ x) + ρ x * (c * ‖h2_perp x‖ ^ 2 - C) / θ) := by
      ring
    have e2 : ρ x * (C / θ - a * ‖h2_perp x‖ ^ 2) = - (ρ x * (c * ‖h2_perp x‖ ^ 2 - C) / θ) := by
      simp only [ha]; field_simp; ring
    rw [e]
    nlinarith [ht, e2, hρ0 x]
  have hρU : Integrable (fun x => ρ x * U x) (volume.restrict (cep_cell N)) := by
    have : (fun x => ρ x * U x) = fun x => θ * (ρ x * (U x - (c * ‖h2_perp x‖ ^ 2 - C)) / θ) +
        (c * (ρ x * ‖h2_perp x‖ ^ 2) - C * ρ x) := by
      funext x; field_simp; ring
    rw [this]
    exact (hI.const_mul θ).add ((hρr.const_mul c).sub (hρi.const_mul C))
  refine ⟨hρU, ?_⟩
  have : (fun x => ρ x * Real.log (ρ x)) = fun x => (ρ x * Real.log (ρ x) + ρ x * U x / θ) - (1 / θ) * (ρ x * U x) := by
    funext x; field_simp; ring
  rw [this]
  exact hΦ.sub (hρU.const_mul _)

/-- The mollified free energy is below the entropy up to an explicit error. -/
theorem h2_free_le {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) (hUper : ∀ z, U (z + cep_diag N) = U z) {K : ℝ≥0}
    (hK : LipschitzWith K (gradient U))
    (hconf : ∃ c C : ℝ, 0 < c ∧ ∀ z, c * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ U z)
    {θ : ℝ} (hθ : 0 < θ) {ρ : Ch N → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫⁻ x in cep_cell N, ENNReal.ofReal (ρ x) = 1)
    (hΦ : Integrable (fun x => ρ x * Real.log (ρ x) + ρ x * U x / θ) (volume.restrict (cep_cell N)))
    (hmom : Integrable (fun y => ‖h2_perp y‖ ^ 2) (h2_dMeas ρ)) {v : ℝ} (hv : 0 < v) {η : ℝ} (hη : 0 < η) :
    h2_free θ U (h2_mu v (h2_dMeas ρ)) ≤
      (∫ x in cep_cell N, (ρ x * Real.log (ρ x) + ρ x * U x / θ)) +
        (η / 2 * ∫ y, ‖gradient U y‖ ^ 2 ∂(h2_dMeas ρ) + ((K : ℝ) / 2 + 1 / (2 * η)) * (N * v)) / θ := by
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by norm_num)
  haveI := h2_dMeas_prob hρ1
  set μ : Measure (Ch N) := h2_dMeas ρ with hμ
  obtain ⟨c0, C, hc0, hCl⟩ := hconf
  have hC : ∀ z, 0 ≤ U z + C := fun z => by
    have := hCl z
    nlinarith [mul_nonneg hc0.le (sq_nonneg (Metric.infDist z (cep_Alcove N)))]
  obtain ⟨hρU, hρL⟩ := h2_density_Uint hU.continuous ⟨c0, C, hc0, hCl⟩ hθ hρ hρ0 hρ1 hΦ hmom
  have hρi := h2_integrable_of_lintegral hρ hρ0 hρ1
  have hUC : Integrable (fun y => U y + C) μ := by
    rw [hμ, h2_integrable_dMeas_iff hρ hρ0]
    have : (fun x => ρ x * (U x + C)) = fun x => ρ x * U x + C * ρ x := by funext x; ring
    rw [this]; exact hρU.add (hρi.const_mul C)
  have hG := (h2_integrable_grad hUper hK hU1 hmom).2
  obtain ⟨hI1, hI2⟩ := h2_U_term hU1 hUper hK hC hv hη μ hUC hG
  have hu1 : IntegrableOn (h2_mu v μ) (cep_cell N) := h2_integrableOn_cell_mu hv μ
  have hint1 : ∫ x in cep_cell N, h2_mu v μ x = 1 := h2_integral_cell_mu hv μ
  have hΦu := h2_integrable_Phi_single hθ hv hU hUper hK μ (h2_dMeas_compl ρ) hmom
  have hUu : Integrable (fun x => h2_mu v μ x * U x) (volume.restrict (cep_cell N)) := by
    have : (fun x => h2_mu v μ x * U x) = fun x => h2_mu v μ x * (U x + C) - C * h2_mu v μ x := by
      funext x; ring
    rw [this]; exact hI1.sub (hu1.const_mul C)
  have hLu : Integrable (fun x => h2_mu v μ x * Real.log (h2_mu v μ x)) (volume.restrict (cep_cell N)) := by
    have : (fun x => h2_mu v μ x * Real.log (h2_mu v μ x)) =
        fun x => (h2_mu v μ x * Real.log (h2_mu v μ x) + h2_mu v μ x * U x / θ) - (1 / θ) * (h2_mu v μ x * U x) := by
      funext x; field_simp; ring
    rw [this]; exact hΦu.sub (hUu.const_mul _)
  have hJ := h2_entropy_term_le hv hρ hρ0 hρ1 hρL hLu
  -- potential term
  have hUint : ∫ x in cep_cell N, h2_mu v μ x * U x ≤
      (∫ x in cep_cell N, ρ x * U x) + (η / 2 * ∫ y, ‖gradient U y‖ ^ 2 ∂μ + ((K : ℝ) / 2 + 1 / (2 * η)) * (N * v)) := by
    have e1 : ∫ x in cep_cell N, h2_mu v μ x * U x =
        (∫ x in cep_cell N, h2_mu v μ x * (U x + C)) - C := by
      have : (fun x => h2_mu v μ x * U x) = fun x => h2_mu v μ x * (U x + C) - C * h2_mu v μ x := by
        funext x; ring
      rw [this, integral_sub hI1 (hu1.const_mul C), integral_const_mul, hint1]; ring
    have e2 : ∫ y, (U y + C) ∂μ = (∫ x in cep_cell N, ρ x * U x) + C := by
      rw [hμ, h2_integral_dMeas hρ hρ0]
      have : (fun x => ρ x * (U x + C)) = fun x => ρ x * U x + C * ρ x := by funext x; ring
      rw [this, integral_add hρU (hρi.const_mul C), integral_const_mul,
        h2_integral_of_lintegral hρ hρ0 hρ1]; ring
    rw [e1]
    linarith [hI2, e2]
  have e3 : h2_free θ U (h2_mu v μ) = (∫ x in cep_cell N, h2_mu v μ x * Real.log (h2_mu v μ x)) +
      (1 / θ) * ∫ x in cep_cell N, h2_mu v μ x * U x := by
    unfold h2_free
    have : (fun x => h2_mu v μ x * Real.log (h2_mu v μ x) + h2_mu v μ x * U x / θ) =
        fun x => h2_mu v μ x * Real.log (h2_mu v μ x) + (1 / θ) * (h2_mu v μ x * U x) := by
      funext x; field_simp
    rw [this, integral_add hLu (hUu.const_mul _), integral_const_mul]
  have e4 : (∫ x in cep_cell N, (ρ x * Real.log (ρ x) + ρ x * U x / θ)) =
      (∫ x in cep_cell N, ρ x * Real.log (ρ x)) + (1 / θ) * ∫ x in cep_cell N, ρ x * U x := by
    have : (fun x => ρ x * Real.log (ρ x) + ρ x * U x / θ) =
        fun x => ρ x * Real.log (ρ x) + (1 / θ) * (ρ x * U x) := by
      funext x; field_simp
    rw [this, integral_add hρL (hρU.const_mul _), integral_const_mul]
  rw [e3, e4]
  have hθi : 0 < 1 / θ := by positivity
  have := mul_le_mul_of_nonneg_left hUint hθi.le
  have e5 : (η / 2 * ∫ y, ‖gradient U y‖ ^ 2 ∂μ + ((K : ℝ) / 2 + 1 / (2 * η)) * (N * v)) / θ =
      (1 / θ) * (η / 2 * ∫ y, ‖gradient U y‖ ^ 2 ∂μ + ((K : ℝ) / 2 + 1 / (2 * η)) * (N * v)) := by ring
  rw [e5]
  nlinarith [this, hJ]

end HRS.MC.CepH2
