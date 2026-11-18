import HRS.MS.SA12X3N1E

/-!
# S.A.12 N1/N2 (SA12X3), part F: bounds of the remainder `∫ q(L⁻¹ w) Q(x - w) dw` of the near identity
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

theorem sa12x3n_int_le {F : Euc d → ℝ} {x : Euc d} {R A : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ w ∈ closedBall x R, |F w| ≤ A) (hz : ∀ w ∉ closedBall x R, F w = 0) :
    |∫ w, F w| ≤ A * (volume (closedBall (0 : Euc d) R)).toReal := by
  have hpt : ∀ w, ‖F w‖ ≤ (closedBall x R).indicator (fun _ => A) w := by
    intro w
    by_cases hw : w ∈ closedBall x R
    · rw [indicator_of_mem hw, Real.norm_eq_abs]; exact hA w hw
    · rw [indicator_of_notMem hw, hz w hw]; simp
  have hind : Integrable ((closedBall x R).indicator (fun _ => A)) volume :=
    (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const measure_closedBall_lt_top.ne)
  have := norm_integral_le_of_norm_le hind (Filter.Eventually.of_forall hpt)
  rw [Real.norm_eq_abs] at this
  refine this.trans ?_
  rw [integral_indicator measurableSet_closedBall, setIntegral_const]
  simp only [smul_eq_mul]
  rw [Measure.real, Measure.addHaar_closedBall_center]
  nlinarith [ENNReal.toReal_nonneg (a := volume (closedBall (0 : Euc d) R))]

theorem sa12x3n_E_bounds {q : Euc d → ℝ} (hq : ContDiff ℝ ∞ q) (δ : ℝ) :
    ∃ Mq Lq : ℝ, 0 ≤ Mq ∧ 0 ≤ Lq ∧ ∀ L : ℝ, 0 < L → ∀ R : ℝ, 0 ≤ R → ∀ Q : Euc d → ℝ, Continuous Q →
      tsupport Q ⊆ closedBall 0 R → ∫ u, Q u = 0 → ∀ B : ℝ, (∀ u, |Q u| ≤ B) → ∀ x : Euc d, ‖x‖ + R < δ * L →
        |∫ w, q (L⁻¹ • w) * Q (x - w)| ≤ Mq * (B * (volume (closedBall (0 : Euc d) R)).toReal) ∧
        |∫ w, q (L⁻¹ • w) * Q (x - w)| ≤ Lq * (R / L) * (B * (volume (closedBall (0 : Euc d) R)).toReal) := by
  have hK : IsCompact (closedBall (0 : Euc d) δ) := isCompact_closedBall _ _
  obtain ⟨M1, hM1⟩ := hK.exists_bound_of_continuousOn hq.continuous.continuousOn
  obtain ⟨M2, hM2⟩ := hK.exists_bound_of_continuousOn
    ((hq.continuous_fderiv (by simp)).continuousOn)
  refine ⟨|M1|, |M2|, abs_nonneg _, abs_nonneg _, fun L hL R hR Q hQ hQs hQ0 B hB x hx => ?_⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hzero : ∀ w ∉ closedBall x R, Q (x - w) = 0 := by
    intro w hw
    by_contra h
    apply hw
    have := hQs (subset_tsupport Q h)
    rw [mem_closedBall, dist_zero_right] at this
    rw [mem_closedBall, dist_eq_norm, norm_sub_rev]; exact this
  have hwδ : ∀ w ∈ closedBall x R, ‖L⁻¹ • w‖ ≤ δ := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    have h1 : ‖w‖ ≤ ‖x‖ + R := by
      calc ‖w‖ = ‖x - (x - w)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖x‖ + ‖x - w‖ := norm_sub_le _ _
        _ ≤ _ := by rw [norm_sub_rev] at hw; linarith
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hL, inv_mul_le_iff₀ hL]
    linarith
  constructor
  · refine (sa12x3n_int_le (F := fun w => q (L⁻¹ • w) * Q (x - w)) (x := x) (R := R) (A := |M1| * B)
      (mul_nonneg (abs_nonneg _) hB0) (fun w hw => ?_) (fun w hw => by simp only [hzero w hw]; simp)).trans
      (le_of_eq (by ring))
    show |q (L⁻¹ • w) * Q (x - w)| ≤ _
    rw [abs_mul]
    exact mul_le_mul (le_trans (by simpa [Real.norm_eq_abs] using hM1 _ (mem_closedBall_zero_iff.2 (hwδ w hw)))
      (le_abs_self _)) (hB _) (abs_nonneg _) (abs_nonneg _)
  · have hQi : Integrable (fun w => Q (x - w)) volume :=
      hQ.comp (continuous_const.sub continuous_id) |>.integrable_of_hasCompactSupport
        ((HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 R)
          ((subset_tsupport Q).trans hQs)).comp_homeomorph (Homeomorph.subLeft x))
    have hint0 : ∫ w, Q (x - w) = 0 := by
      have h := integral_sub_left_eq_self (μ := volume) Q x
      rw [h, hQ0]
    have hqi : Integrable (fun w : Euc d => q (L⁻¹ • w) * Q (x - w)) volume := by
      refine (Continuous.integrable_of_hasCompactSupport ?_ ?_)
      · exact (hq.continuous.comp (continuous_const_smul L⁻¹)).mul (hQ.comp (continuous_const.sub continuous_id))
      · exact (((HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 R)
          ((subset_tsupport Q).trans hQs)).comp_homeomorph (Homeomorph.subLeft x))).mul_left
    have hsplit : ∫ w, q (L⁻¹ • w) * Q (x - w) = ∫ w, (q (L⁻¹ • w) - q (L⁻¹ • x)) * Q (x - w) := by
      have : ∀ w, (q (L⁻¹ • w) - q (L⁻¹ • x)) * Q (x - w) =
          q (L⁻¹ • w) * Q (x - w) - q (L⁻¹ • x) * Q (x - w) := fun w => by ring
      simp_rw [this]
      rw [integral_sub hqi (hQi.const_mul _), integral_const_mul, hint0]
      ring
    rw [hsplit]
    have hxδ : ‖L⁻¹ • x‖ ≤ δ := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hL, inv_mul_le_iff₀ hL]
      nlinarith
    have hmvt : ∀ w ∈ closedBall x R, |q (L⁻¹ • w) - q (L⁻¹ • x)| ≤ |M2| * (R / L) := by
      intro w hw
      have hdiff : ∀ v ∈ closedBall (0 : Euc d) δ, DifferentiableAt ℝ q v := fun v _ =>
        (hq.differentiable (by simp)) v
      have hb : ∀ v ∈ closedBall (0 : Euc d) δ, ‖fderiv ℝ q v‖ ≤ |M2| := fun v hv =>
        (hM2 v hv).trans (le_abs_self _)
      have := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hb (convex_closedBall (0 : Euc d) δ)
        (mem_closedBall_zero_iff.2 hxδ) (mem_closedBall_zero_iff.2 (hwδ w hw))
      rw [Real.norm_eq_abs] at this
      refine this.trans ?_
      rw [← smul_sub, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hL]
      have hw' : ‖w - x‖ ≤ R := by
        rw [mem_closedBall, dist_eq_norm] at hw; exact hw
      calc |M2| * (L⁻¹ * ‖w - x‖) ≤ |M2| * (L⁻¹ * R) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw' (inv_nonneg.2 hL.le)) (abs_nonneg _)
        _ = _ := by field_simp
    refine (sa12x3n_int_le (F := fun w => (q (L⁻¹ • w) - q (L⁻¹ • x)) * Q (x - w)) (x := x) (R := R)
      (A := |M2| * (R / L) * B) (mul_nonneg (mul_nonneg (abs_nonneg _) (div_nonneg hR hL.le)) hB0)
      (fun w hw => ?_) (fun w hw => by simp only [hzero w hw]; simp)).trans (le_of_eq (by ring))
    show |(q (L⁻¹ • w) - q (L⁻¹ • x)) * Q (x - w)| ≤ _
    rw [abs_mul]
    exact mul_le_mul (hmvt w hw) (hB _) (abs_nonneg _) (by positivity)

end HRS.MH.AdjointRd.Phase2SA12Construction
