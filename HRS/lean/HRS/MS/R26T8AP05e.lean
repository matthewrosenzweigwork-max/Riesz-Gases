import HRS.MS.R26T8AP05d

/-!
# S8.2 local Newton layer, packet T8A.P05 (part e): scale-free kernel majorant and support of the nested source jet
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

/-- Constant subtracted from the Newton kernel in the comparable annulus (only `d = 2`, `q >= 1`). -/
def r26t8a_kappa (d : ℕ) (nu R : ℝ) (q : ℕ) : ℝ :=
  if d = 2 ∧ q ≠ 0 then (2 * nu * sphereArea d)⁻¹ * (-Real.log R) else 0

/-- Scale-free profile: `|log |v||` for `d = 2` and `|v|^(2-d)` otherwise. -/
def r26t8a_p05_G (d : ℕ) (v : Euc d) : ℝ := if d = 2 then |Real.log ‖v‖| else ‖v‖ ^ (2 - (d : ℝ))

def r26t8a_cK (d : ℕ) (nu : ℝ) : ℝ :=
  if d = 2 then |(2 * nu * sphereArea d)⁻¹| else |(2 * nu * ((d : ℝ) - 2) * sphereArea d)⁻¹|

theorem r26t8a_cK_nonneg (d : ℕ) (nu : ℝ) : 0 ≤ r26t8a_cK d nu := by
  unfold r26t8a_cK; split_ifs <;> exact abs_nonneg _

theorem r26t8a_G_nonneg (d : ℕ) (v : Euc d) : 0 ≤ r26t8a_p05_G d v := by
  unfold r26t8a_p05_G; split_ifs
  · exact abs_nonneg _
  · exact Real.rpow_nonneg (norm_nonneg _) _

theorem r26t8a_G_integrableOn (hd : 2 ≤ d) : IntegrableOn (r26t8a_p05_G d) (Metric.ball (0 : Euc d) 7) := by
  by_cases h2 : d = 2
  · subst h2
    have hI := r26t8a_integrableOn_ball_rpow (d := 2) (by norm_num) (α := 1) (by norm_num) 7
    have hc : IntegrableOn (fun _ : Euc 2 => (7 : ℝ)) (Metric.ball 0 7) :=
      integrableOn_const (Metric.isBounded_ball.measure_lt_top.ne)
    have hm : Measurable (r26t8a_p05_G 2) := by
      unfold r26t8a_p05_G; simp only [↓reduceIte]
      exact (Real.measurable_log.comp measurable_norm).abs
    refine Integrable.mono' (hI.add hc) hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' Metric.isOpen_ball.measurableSet).2 (Eventually.of_forall fun v hv => ?_)
    have hv' : ‖v‖ < 7 := by simpa using hv
    unfold r26t8a_p05_G; simp only [↓reduceIte]
    rw [Real.norm_eq_abs, abs_abs]
    by_cases hv0 : v = 0
    · subst hv0; simp
    · exact r26t8a_abs_log_le_inv (norm_pos_iff.2 hv0) hv'.le
  · have hd3 : (2 : ℝ) < d := by
      have : 3 ≤ d := by omega
      exact_mod_cast this
    have hI := r26t8a_integrableOn_ball_rpow (d := d) (by omega) (α := (d : ℝ) - 2) (by linarith) 7
    have hm : Measurable (r26t8a_p05_G d) := by
      unfold r26t8a_p05_G; simp only [h2, ↓reduceIte]
      exact measurable_norm.pow_const _
    refine Integrable.mono' hI hm.aestronglyMeasurable (Eventually.of_forall fun v => ?_)
    unfold r26t8a_p05_G; simp only [h2, ↓reduceIte]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), show -((d : ℝ) - 2) = 2 - (d : ℝ) by ring]

/-- Pointwise majorant of the (shifted) Newton kernel in terms of the scale-free profile. -/
theorem r26t8a_K_sub_bound (nu : ℝ) {R : ℝ} (hR : 0 < R) (q : ℕ) {u : Euc d} (hu : u ≠ 0) :
    |newtonKernel d nu u - r26t8a_kappa d nu R q| ≤
      r26t8a_cK d nu * (R ^ (2 - (d : ℝ)) * r26t8a_p05_G d (R⁻¹ • u) + if d = 2 ∧ q = 0 then |Real.log R| else 0) := by
  have hn : 0 < ‖u‖ := norm_pos_iff.2 hu
  have hsn : ‖R⁻¹ • u‖ = R⁻¹ * ‖u‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)]
  have hsn0 : 0 < ‖R⁻¹ • u‖ := by rw [hsn]; positivity
  by_cases h2 : d = 2
  · subst h2
    have hK : newtonKernel 2 nu u = (2 * nu * sphereArea 2)⁻¹ * (-Real.log ‖u‖) := by
      simp [newtonKernel, div_eq_inv_mul]
    have hlog : Real.log ‖u‖ = Real.log R + Real.log ‖R⁻¹ • u‖ := by
      rw [hsn, Real.log_mul (inv_ne_zero hR.ne') hn.ne', Real.log_inv]; ring
    have hG : r26t8a_p05_G 2 (R⁻¹ • u) = |Real.log ‖R⁻¹ • u‖| := by simp [r26t8a_p05_G]
    have hcK : r26t8a_cK 2 nu = |(2 * nu * sphereArea 2)⁻¹| := by simp [r26t8a_cK]
    rw [hG, hcK]
    simp only [Nat.cast_ofNat, sub_self, Real.rpow_zero, one_mul, true_and]
    by_cases hq : q = 0
    · simp only [r26t8a_kappa, hq, ne_eq, not_true_eq_false, and_false, if_false, sub_zero, if_true, hK]
      rw [abs_mul, abs_neg, hlog]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      exact (abs_add_le (Real.log R) (Real.log ‖R⁻¹ • u‖)).trans_eq (add_comm _ _)
    · simp only [r26t8a_kappa, hq, ne_eq, not_false_eq_true, and_self, if_true, hK, if_false, add_zero]
      rw [hlog, ← mul_sub, abs_mul]
      refine le_of_eq (congrArg _ ?_)
      rw [← abs_neg]; congr 1; ring
  · have hK : newtonKernel d nu u = (2 * nu * ((d : ℝ) - 2) * sphereArea d)⁻¹ * ‖u‖ ^ (2 - (d : ℝ)) := by
      simp [newtonKernel, h2, div_eq_inv_mul]
    have hG : r26t8a_p05_G d (R⁻¹ • u) = ‖R⁻¹ • u‖ ^ (2 - (d : ℝ)) := by simp [r26t8a_p05_G, h2]
    have hcK : r26t8a_cK d nu = |(2 * nu * ((d : ℝ) - 2) * sphereArea d)⁻¹| := by simp [r26t8a_cK, h2]
    have hκ : r26t8a_kappa d nu R q = 0 := by simp [r26t8a_kappa, h2]
    have hu' : ‖u‖ = R * ‖R⁻¹ • u‖ := by rw [hsn]; field_simp
    rw [hκ, sub_zero, hK, hG, hcK]
    simp only [h2, false_and, if_false, add_zero]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hn.le _), hu', Real.mul_rpow hR.le hsn0.le]

end HRS.MS.R26T8A
