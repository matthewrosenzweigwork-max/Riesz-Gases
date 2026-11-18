import HRS.MS.WrEntAux1

/-!
# S11.3.E1 (breakdown packet E1): power and logarithmic integrability of bounded nonnegative ratios;
# the normalized power measure `s113_powerTilt` and its mass `s113_powerMass`
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.S113BD

section Entropy

variable {α : Type*} [MeasurableSpace α]

/-- The real power mass, used only after integrability and positivity are proved. -/
def s113_powerMass (Q : Measure α) (r : α → ℝ) (p : ℝ) : ℝ :=
  ∫ x, r x ^ p ∂Q

/-- The normalized power measure in the localized calculation. -/
def s113_powerTilt (Q : Measure α) (r : α → ℝ) (p : ℝ) : Measure α :=
  Q.withDensity (fun x => ENNReal.ofReal (r x ^ p / s113_powerMass Q r p))

/-- `z^p log z` is bounded on `[0,B]` for `p > 1`. -/
theorem s113_pow_log_bound (p B : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, ∀ z : ℝ, 0 ≤ z → z ≤ B → |z ^ p * Real.log z| ≤ C := by
  have hcont : Continuous fun z : ℝ => z ^ (p - 1) * (z * Real.log z) :=
    (Real.continuous_rpow_const (by linarith)).mul Real.continuous_mul_log
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := B)).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨C, fun z hz0 hzB => ?_⟩
  have e : z ^ p * Real.log z = z ^ (p - 1) * (z * Real.log z) := by
    rcases hz0.eq_or_lt with h | h
    · subst h
      simp [Real.zero_rpow (by linarith : p ≠ 0)]
    · rw [Real.rpow_sub_one h.ne']
      field_simp
  rw [e]
  have := hC z ⟨hz0, hzB⟩
  simpa using this

theorem s113_power_integrable (Q : Measure α) [IsProbabilityMeasure Q]
    (r : α → ℝ) (hr : Measurable r) (hr0 : ∀ x, 0 ≤ r x)
    (p B : ℝ) (hp : 1 < p) (hB : ∀ x, r x ≤ B) :
    Integrable (fun x => r x ^ p) Q ∧
      Integrable (fun x => r x ^ p * Real.log (r x)) Q ∧
      Measurable (fun x => ENNReal.ofReal (r x ^ p)) := by
  have hm1 : Measurable fun x => r x ^ p := hr.pow_const p
  refine ⟨?_, ?_, ENNReal.measurable_ofReal.comp hm1⟩
  · refine Integrable.mono' (integrable_const (B ^ p)) hm1.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (hr0 x) p)]
    exact Real.rpow_le_rpow (hr0 x) (hB x) (by linarith)
  · obtain ⟨C, hC⟩ := s113_pow_log_bound p B hp
    refine Integrable.mono' (integrable_const C)
      (hm1.mul (Real.measurable_log.comp hr)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact hC (r x) (hr0 x) (hB x)

end Entropy

end HRS.MS.S113BD
