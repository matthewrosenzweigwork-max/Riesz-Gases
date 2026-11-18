import HRS.Main.ThermAux6

/-!
# THERM helper 7: bias bound from the `L²` marginal density estimate
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d N : ℕ}

theorem therm_bias_bound {μ π : Measure (Torus d)} [IsProbabilityMeasure μ] [IsProbabilityMeasure π]
    (hπ : π ≪ μ) {f : Torus d → ℝ} (hfm : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) {e : ℝ}
    (he : 0 ≤ e)
    (hL2 : eLpNorm (fun y => (π.rnDeriv μ y).toReal - 1) 2 μ ≤ ENNReal.ofReal e) :
    |∫ x, f x ∂π - ∫ x, f x ∂μ| ≤ B * e := by
  set h : Torus d → ℝ := fun y => (π.rnDeriv μ y).toReal with hh
  have hhm : Measurable h := (Measure.measurable_rnDeriv π μ).ennreal_toReal
  have hhi : Integrable h μ := Measure.integrable_toReal_rnDeriv
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hfi : Integrable f μ :=
    Integrable.of_bound hfm.aestronglyMeasurable B (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hB x)
  have hhfi : Integrable (fun x => h x * f x) μ := by
    refine Integrable.mono' (hhi.norm.mul_const B) (hhm.mul hfm).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs (f x)]
    exact mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _)
  have hdiff : ∫ x, f x ∂π - ∫ x, f x ∂μ = ∫ x, (h x - 1) * f x ∂μ := by
    rw [← integral_toReal_rnDeriv_mul hπ (f := f)]
    rw [← integral_sub hhfi hfi]
    congr 1
    funext x
    ring
  have hg : AEStronglyMeasurable (fun y => h y - 1) μ := (hhm.sub_const 1).aestronglyMeasurable
  have h1 : ENNReal.ofReal |∫ x, (h x - 1) * f x ∂μ| ≤ ENNReal.ofReal B * ENNReal.ofReal e := by
    calc ENNReal.ofReal |∫ x, (h x - 1) * f x ∂μ|
        = ‖∫ x, (h x - 1) * f x ∂μ‖ₑ := by rw [← Real.norm_eq_abs, ofReal_norm_eq_enorm]
      _ ≤ ∫⁻ x, ‖(h x - 1) * f x‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ x, ‖h x - 1‖ₑ * ENNReal.ofReal B ∂μ := by
          refine lintegral_mono fun x => ?_
          rw [enorm_mul]
          gcongr
          rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
          exact ENNReal.ofReal_le_ofReal (hB x)
      _ = eLpNorm (fun y => h y - 1) 1 μ * ENNReal.ofReal B := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, eLpNorm_one_eq_lintegral_enorm]
          all_goals exact hg
      _ ≤ ENNReal.ofReal e * ENNReal.ofReal B := by
          gcongr
          · exact (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans hL2
          all_goals exact hg
      _ = _ := mul_comm _ _
  rw [hdiff, ← ENNReal.ofReal_mul hB0] at *
  have := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB0 he)).1 h1
  exact this

end Main

end HRS
