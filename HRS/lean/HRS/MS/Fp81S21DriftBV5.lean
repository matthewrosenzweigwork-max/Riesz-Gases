import HRS.MS.Fp81S21DriftBV4

/-! Drift and covariance interval operators as BV transports. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Set MeasureTheory
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.S111K2

variable {d r : ℕ} {Pw : ℝ} {E : r26t6_WeightedChart d r Pw} {C : WholeCoeff d}
  {T u c0 B H b h : ℝ} (O : r26t6_IntervalOperators E C T u c0 B)
  (hH : 0 ≤ H) (hb : 0 ≤ b) (hh : 0 ≤ h) (hhH : h ≤ H)
  (hbQ : b + h ≤ u + T) (hB : 0 ≤ B) (hc : 0 ≤ c0)

include hB hc in
private theorem drift_unweighted {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w)
    (hw : w ≤ u + T) (q : r26t6_TimeCoeff (u + T)) :
    ‖O.drift v w q‖ ≤ B * ∫ z in Ioc v w, ‖q z‖ := by
  apply (O.drift_norm v w hv hvw hw q).trans
  apply mul_le_mul_of_nonneg_left _ hB
  apply fp81s21_weighted_interval_le hv hw q (fun z => s111k2_age c0 u z)
  · exact fun z => (fp81s21_age_bounds hc z).1
  · exact fun z => (fp81s21_age_bounds hc z).2
  · unfold s111k2_age
    fun_prop

include hB hc in
private theorem covariance_unweighted {v w : ℝ} (hv : 0 ≤ v) (hvw : v ≤ w)
    (hw : w ≤ u + T) (q : r26t6_TimeCoeff (u + T)) :
    ‖O.covariance v w q‖ ≤ (B * |2 * C.ν|) * ∫ z in Ioc v w, ‖q z‖ := by
  apply (O.covariance_norm v w hv hvw hw q).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB (abs_nonneg _))
  apply fp81s21_weighted_interval_le hv hw q (fun z => s111k2_age c0 u z ^ 2)
  · exact fun z => sq_nonneg _
  · exact fun z => pow_le_one₀ (fp81s21_age_bounds hc z).1 (fp81s21_age_bounds hc z).2
  · unfold s111k2_age
    fun_prop

include O hb hh hhH hbQ hB hc in
/-- Drift accumulated up to the clipped source time, in the variation norm. -/
def fp81s21_driftBV : r26t6_TimeCoeff (u + T) →L[ℝ] fp81s21_BV0 (E := R2X d T) hH :=
  fp81s21_intervalBV hH
    (fp81s21_clippedIntervalBVData hH hb hh hhH hbQ hB O.drift O.drift_zero
      O.drift_add O.drift_cont (fun v w hv hvw hw q => drift_unweighted O hB hc hv hvw hw q)) hB

theorem fp81s21_driftBV_apply (q : r26t6_TimeCoeff (u + T)) (s : Icc (0 : ℝ) H) :
    fp81s21_bvPath hH (fp81s21_driftBV O hH hb hh hhH hbQ hB hc q) s =
      O.drift b (b + min (s : ℝ) h) q := by
  simp [fp81s21_driftBV, fp81s21_intervalBV_apply, fp81s21_clippedIntervalBVData,
    fp81s21_clippedDelta, min_eq_left hh]

theorem fp81s21_driftBV_norm_le : ‖fp81s21_driftBV O hH hb hh hhH hbQ hB hc‖ ≤ B := by
  exact fp81s21_intervalBV_norm_le hH _ hB

include O hb hh hhH hbQ hB hc in
/-- Covariance accumulated up to the clipped source time, in the variation norm. -/
def fp81s21_covarianceBV : r26t6_TimeCoeff (u + T) →L[ℝ]
    fp81s21_BV0 (E := projTensor (R2X d T) 2) hH :=
  fp81s21_intervalBV hH
    (fp81s21_clippedIntervalBVData hH hb hh hhH hbQ (mul_nonneg hB (abs_nonneg _))
      O.covariance O.covariance_zero O.covariance_add O.covariance_cont
      (fun v w hv hvw hw q => covariance_unweighted O hB hc hv hvw hw q))
    (mul_nonneg hB (abs_nonneg _))

theorem fp81s21_covarianceBV_apply (q : r26t6_TimeCoeff (u + T)) (s : Icc (0 : ℝ) H) :
    fp81s21_bvPath hH (fp81s21_covarianceBV O hH hb hh hhH hbQ hB hc q) s =
      O.covariance b (b + min (s : ℝ) h) q := by
  simp [fp81s21_covarianceBV, fp81s21_intervalBV_apply, fp81s21_clippedIntervalBVData,
    fp81s21_clippedDelta, min_eq_left hh]

theorem fp81s21_covarianceBV_norm_le :
    ‖fp81s21_covarianceBV O hH hb hh hhH hbQ hB hc‖ ≤ B * |2 * C.ν| := by
  exact fp81s21_intervalBV_norm_le hH _ (mul_nonneg hB (abs_nonneg _))

#print axioms fp81s21_driftBV
#print axioms fp81s21_driftBV_apply
#print axioms fp81s21_driftBV_norm_le
#print axioms fp81s21_covarianceBV
#print axioms fp81s21_covarianceBV_apply
#print axioms fp81s21_covarianceBV_norm_le
end HRS.Fp81.S21
end
