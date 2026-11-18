import HRS.Commutator.Torus.TSAMPAux21

/-!
# T-SAMP helpers, part 22: the `L^q` norm of the near part of a kernel
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

/-- The constant `∫_{|y|<1} |y|^{b}`. -/
def tsampIa (d : ℕ) (b : ℝ) : ℝ := ∫ y : Euc d in Metric.ball (0 : Euc d) 1, ‖y‖ ^ b

lemma tsamp_integrable_ballpow (hd : 1 ≤ d) {b : ℝ} (hb : -(d : ℝ) < b) :
    Integrable ((Metric.ball (0 : Euc d) 1).indicator fun y : Euc d => ‖y‖ ^ b) := by
  have h1 : IntegrableOn (fun y : Euc d => ‖y‖ ^ b) (Metric.ball (0 : Euc d) 1) volume := by
    refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := -b) (r := 1)
      (by rw [finrank_euclideanSpace_fin]; exact hd) (by rw [finrank_euclideanSpace_fin]; linarith) ?_ ?_
    · exact Eventually.of_forall fun x => by
        rw [one_mul, neg_neg, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)]
    · exact (measurable_norm.pow_const _).aestronglyMeasurable
  exact (integrable_indicator_iff measurableSet_ball).2 h1

lemma tsamp_Ia_nonneg (b : ℝ) : 0 ≤ tsampIa d b :=
  integral_nonneg fun y => Real.rpow_nonneg (norm_nonneg y) _

lemma tsamp_near_lintegral (hd : 1 ≤ d) {η : ℝ} (hη : 0 < η) {a q c : ℝ} (hq : 0 < q)
    (haq : -(d : ℝ) < a * q) (hc : 0 ≤ c) :
    ∫⁻ z : Torus d, (if KernelGrad.tdist z 0 < η then ENNReal.ofReal (c * KernelGrad.tdist z 0 ^ a) else 0) ^ q ≤
      ENNReal.ofReal (c ^ q * η ^ (a * q) * η ^ d * tsampIa d (a * q)) := by
  set F : ℝ → ℝ≥0∞ := fun t => (if t < η then ENNReal.ofReal (c * t ^ a) else 0) ^ q with hF
  have hFm : Measurable F := by
    have : Measurable fun t : ℝ => if t < η then ENNReal.ofReal (c * t ^ a) else 0 :=
      Measurable.ite measurableSet_Iio (by fun_prop) measurable_const
    exact this.pow_const q
  refine (tsamp_tdist_lintegral_le hFm).trans ?_
  set G : Euc d → ℝ := (Metric.ball (0 : Euc d) 1).indicator fun y : Euc d => ‖y‖ ^ (a * q) with hG
  have hGi := tsamp_integrable_ballpow hd haq
  set h : Euc d → ℝ := fun x => c ^ q * η ^ (a * q) * G (η⁻¹ • x) with hh
  have hhi : Integrable h := (hGi.comp_smul (inv_ne_zero hη.ne')).const_mul _
  have hpt : ∀ x : Euc d, F ‖x‖ = ENNReal.ofReal (h x) := by
    intro x
    simp only [hF, hh, hG]
    by_cases hx : ‖x‖ < η
    · have hx' : η⁻¹ • x ∈ Metric.ball (0 : Euc d) 1 := by
        rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hη), inv_mul_eq_div,
          div_lt_one hη]
        exact hx
      rw [if_pos hx, Set.indicator_of_mem hx']
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hq.le]
      congr 1
      have hn : ‖η⁻¹ • x‖ = ‖x‖ / η := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hη), inv_mul_eq_div]
      rw [hn, Real.mul_rpow hc (Real.rpow_nonneg (norm_nonneg x) _), ← Real.rpow_mul (norm_nonneg x),
        Real.div_rpow (norm_nonneg x) hη.le]
      have : η ^ (a * q) ≠ 0 := (Real.rpow_pos_of_pos hη _).ne'
      field_simp
    · have hx' : η⁻¹ • x ∉ Metric.ball (0 : Euc d) 1 := by
        rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hη), inv_mul_eq_div,
          div_lt_one hη]
        exact hx
      rw [if_neg hx, Set.indicator_of_notMem hx']
      simp [ENNReal.zero_rpow_of_pos hq]
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hhi (Eventually.of_forall fun x => by
    simp only [hh, hG, Set.indicator]; split_ifs <;> positivity)]
  refine le_of_eq (congrArg ENNReal.ofReal ?_)
  simp only [hh]
  rw [integral_const_mul, MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
    (μ := (volume : Measure (Euc d))) G hη.le, finrank_euclideanSpace_fin, smul_eq_mul]
  have : ∫ y : Euc d, G y = tsampIa d (a * q) := by
    simp only [hG, tsampIa]
    rw [integral_indicator measurableSet_ball]
  rw [this]
  ring

end HRS.Commutator.TorusNote
