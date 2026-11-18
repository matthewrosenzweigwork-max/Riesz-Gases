import HRS.MS.R26T8AP04

/-!
# S8.2 local Newton layer, packet T8A.P05 (part a): local integrability of the Newton kernel and scaling of ball integrals
`r26t8a_K_integrableOn`: the Newton kernel is integrable on balls; `r26t8a_scale_int`: `int_{|u|<7R} G(u/R) du = R^d int_{|v|<7} G`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_integrableOn_ball_rpow (hd : 1 ≤ d) {α : ℝ} (hα : α < d) (r : ℝ) :
    IntegrableOn (fun z : Euc d => ‖z‖ ^ (-α)) (Metric.ball 0 r) := by
  refine integrableOn_ball_of_norm_le_rpow (μ := volume) (f := fun z : Euc d => ‖z‖ ^ (-α)) (C := 1)
    (α := α) (r := r) (by rw [finrank_euclideanSpace_fin]; exact hd)
    (by rw [finrank_euclideanSpace_fin]; exact hα) (Eventually.of_forall fun x => ?_)
    (measurable_norm.pow_const _).aestronglyMeasurable
  rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]

theorem r26t8a_abs_log_le_inv {x ρ : ℝ} (hx : 0 < x) (hxρ : x ≤ ρ) : |Real.log x| ≤ x ^ (-(1 : ℝ)) + ρ := by
  have h1 : x ^ (-(1 : ℝ)) = x⁻¹ := by rw [Real.rpow_neg hx.le, Real.rpow_one]
  rw [h1]
  have hinv : 0 < x⁻¹ := inv_pos.2 hx
  by_cases hx1 : x ≤ 1
  · have : Real.log x⁻¹ ≤ x⁻¹ - 1 := Real.log_le_sub_one_of_pos hinv
    rw [Real.log_inv] at this
    have hl : Real.log x ≤ 0 := Real.log_nonpos hx.le hx1
    rw [abs_of_nonpos hl]
    have : 0 ≤ ρ := hx.le.trans hxρ
    linarith
  · push Not at hx1
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx1.le
    rw [abs_of_nonneg hl]
    have := Real.log_le_sub_one_of_pos hx
    linarith

theorem r26t8a_K_measurable (nu : ℝ) : Measurable (newtonKernel d nu) := by
  unfold newtonKernel
  by_cases h : d = 2
  · simp only [h, ↓reduceIte]
    exact ((Real.measurable_log.comp measurable_norm).neg).div_const _
  · simp only [h, ↓reduceIte]
    exact (measurable_norm.pow_const _).div_const _

theorem r26t8a_K_integrableOn (hd : 2 ≤ d) (nu : ℝ) (ρ : ℝ) :
    IntegrableOn (newtonKernel d nu) (Metric.ball (0 : Euc d) ρ) := by
  by_cases h2 : d = 2
  · subst h2
    have hI := r26t8a_integrableOn_ball_rpow (d := 2) (by norm_num) (α := 1) (by norm_num) ρ
    have hc : IntegrableOn (fun _ : Euc 2 => ρ) (Metric.ball 0 ρ) :=
      integrableOn_const (Metric.isBounded_ball.measure_lt_top.ne)
    refine Integrable.mono' ((hI.add hc).const_mul |(2 * nu * sphereArea 2)⁻¹|)
      (r26t8a_K_measurable nu).aestronglyMeasurable ?_
    refine (ae_restrict_iff' Metric.isOpen_ball.measurableSet).2 (Eventually.of_forall fun u hu => ?_)
    have hu' : ‖u‖ < ρ := by simpa using hu
    have e : newtonKernel 2 nu u = (2 * nu * sphereArea 2)⁻¹ * (-Real.log ‖u‖) := by
      simp [newtonKernel, div_eq_inv_mul]
    rw [e, norm_mul, Real.norm_eq_abs, norm_neg, Real.norm_eq_abs]
    by_cases hu0 : u = 0
    · subst hu0
      have hρ : 0 < ρ := by simpa using hu'
      simp
      positivity
    · have hn : 0 < ‖u‖ := norm_pos_iff.2 hu0
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact r26t8a_abs_log_le_inv hn hu'.le
  · have hd3 : (2 : ℝ) < d := by
      have : 3 ≤ d := by omega
      exact_mod_cast this
    have hI := r26t8a_integrableOn_ball_rpow (d := d) (by omega) (α := (d : ℝ) - 2) (by linarith) ρ
    refine Integrable.mono' (hI.const_mul |(2 * nu * ((d : ℝ) - 2) * sphereArea d)⁻¹|)
      (r26t8a_K_measurable nu).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
    have e : newtonKernel d nu u = (2 * nu * ((d : ℝ) - 2) * sphereArea d)⁻¹ * ‖u‖ ^ (2 - (d : ℝ)) := by
      simp [newtonKernel, h2, div_eq_inv_mul]
    rw [e, norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    rw [show -((d : ℝ) - 2) = 2 - (d : ℝ) by ring]

theorem r26t8a_scale_int {G : Euc d → ℝ} (hG : IntegrableOn G (Metric.ball (0 : Euc d) 7)) {R : ℝ} (hR : 0 < R) :
    Integrable ((Metric.ball (0 : Euc d) (7 * R)).indicator fun u => G (R⁻¹ • u)) ∧
      ∫ u, (Metric.ball (0 : Euc d) (7 * R)).indicator (fun u => G (R⁻¹ • u)) u =
        R ^ d * ∫ v in Metric.ball (0 : Euc d) 7, G v := by
  set G' : Euc d → ℝ := (Metric.ball (0 : Euc d) 7).indicator G with hG'
  have e : (Metric.ball (0 : Euc d) (7 * R)).indicator (fun u => G (R⁻¹ • u)) = fun u => G' (R⁻¹ • u) := by
    funext u
    have hmem : u ∈ Metric.ball (0 : Euc d) (7 * R) ↔ R⁻¹ • u ∈ Metric.ball (0 : Euc d) 7 := by
      simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)]
      rw [inv_mul_lt_iff₀ hR, mul_comm]
    by_cases h : u ∈ Metric.ball (0 : Euc d) (7 * R)
    · rw [Set.indicator_of_mem h, hG', Set.indicator_of_mem (hmem.1 h)]
    · rw [Set.indicator_of_notMem h, hG', Set.indicator_of_notMem (fun h' => h (hmem.2 h'))]
  rw [e]
  refine ⟨(integrable_comp_smul_iff volume G' (inv_ne_zero hR.ne')).2
    ((integrable_indicator_iff Metric.isOpen_ball.measurableSet).2 hG), ?_⟩
  rw [Measure.integral_comp_inv_smul volume G' R, finrank_euclideanSpace_fin, abs_of_pos (pow_pos hR _),
    integral_indicator Metric.isOpen_ball.measurableSet, smul_eq_mul]

end HRS.MS.R26T8A
