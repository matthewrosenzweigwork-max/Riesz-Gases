import HRS.MS.Fp81S21IntervalBV3
import HRS.MS.R26T6CD03

/-! Weight and interval estimates for the interval-operator BV transports. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Set MeasureTheory
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.S111K2

theorem fp81s21_age_bounds {c u : ℝ} (hc : 0 ≤ c) (v : ℝ) :
    0 ≤ s111k2_age c u v ∧ s111k2_age c u v ≤ 1 := by
  constructor
  · exact (Real.exp_pos _).le
  · unfold s111k2_age
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (le_max_right _ _)

theorem fp81s21_weighted_interval_le {Q v w : ℝ} (hv : 0 ≤ v) (hw : w ≤ Q)
    (q : r26t6_TimeCoeff Q) (f : ℝ → ℝ)
    (hf0 : ∀ z, 0 ≤ f z) (hf1 : ∀ z, f z ≤ 1) (hfm : Measurable f) :
    (∫ z in Ioc v w, f z * ‖q z‖) ≤ ∫ z in Ioc v w, ‖q z‖ := by
  have hsub : Ioc v w ⊆ Icc (0 : ℝ) Q := fun z hz => ⟨hv.trans hz.1.le, hz.2.trans hw⟩
  have hI : IntegrableOn (fun z => ‖q z‖) (Icc (0 : ℝ) Q) volume :=
    (Lp.memLp q |>.integrable le_rfl).norm
  have hi : IntegrableOn (fun z => ‖q z‖) (Ioc v w) volume := hI.mono_set hsub
  have hfi : IntegrableOn (fun z => f z * ‖q z‖) (Ioc v w) volume := by
    refine Integrable.mono' hi (hfm.aemeasurable.mul
      (Lp.stronglyMeasurable q).norm.measurable.aemeasurable).aestronglyMeasurable ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf0 z) (norm_nonneg _))]
    simpa using mul_le_mul_of_nonneg_right (hf1 z) (norm_nonneg (q z))
  exact integral_mono hfi hi (fun z => by
    simpa using mul_le_mul_of_nonneg_right (hf1 z) (norm_nonneg (q z)))

#print axioms fp81s21_age_bounds
#print axioms fp81s21_weighted_interval_le
end HRS.Fp81.S21
end
