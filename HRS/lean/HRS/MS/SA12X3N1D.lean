import HRS.MS.SA12X3N1C

/-!
# S.A.12 N1/N2 (SA12X3), part D: far regime of the convolution of a periodic kernel with a mean-zero test function
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

theorem sa12x3n_conv_far (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ R : ℝ, 1 ≤ R → ∀ L : ℝ, 4 * R ≤ L → ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ →
      ∀ Q : Euc d → ℝ, Continuous Q → tsupport Q ⊆ closedBall 0 R → ∫ u, Q u = 0 → ∀ B : ℝ, (∀ u, |Q u| ≤ B) →
        ∀ x : Euc d, (∀ i, |x i| ≤ L / 2) → 2 * R ≤ ‖x‖ →
          |HRS.Whole.convFun γ Q x| ≤ C0 * R * (B * (volume (closedBall (0 : Euc d) R)).toReal) := by
  obtain ⟨C0, hC0, hfar⟩ := sa12x3n_far_diff hd s hs0 hsd
  refine ⟨C0, hC0, fun R hR L hL γ hγ Q hQ hQs hQ0 B hB x hx hxn => ?_⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hQcs : HasCompactSupport Q :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 R)
      ((subset_tsupport Q).trans hQs)
  have hcs' : HasCompactSupport (fun w => Q (x - w)) := hQcs.comp_homeomorph (Homeomorph.subLeft x)
  have hc' : Continuous (fun w => Q (x - w)) := hQ.comp (continuous_const.sub continuous_id)
  have hi : Integrable (fun w => γ w * Q (x - w)) volume :=
    hγ.locInt.integrable_smul_right_of_hasCompactSupport hc' hcs'
  have hconv : HRS.Whole.convFun γ Q x = ∫ w, γ w * Q (x - w) := by
    have h := integral_sub_left_eq_self (μ := volume) (fun t => γ t * Q (x - t)) x
    simp only [sub_sub_cancel] at h
    unfold HRS.Whole.convFun
    rw [← h]
  have hQi : Integrable (fun w => Q (x - w)) volume := hc'.integrable_of_hasCompactSupport hcs'
  have hint0 : ∫ w, Q (x - w) = 0 := by
    have h := integral_sub_left_eq_self (μ := volume) Q x
    rw [h, hQ0]
  have hsplit : ∫ w, γ w * Q (x - w) = ∫ w, (γ w - γ x) * Q (x - w) := by
    have : ∀ w, (γ w - γ x) * Q (x - w) = γ w * Q (x - w) - γ x * Q (x - w) := fun w => by ring
    simp_rw [this]
    rw [integral_sub hi (hQi.const_mul _), integral_const_mul, hint0]
    ring
  rw [hconv, hsplit]
  set V : ℝ := (volume (closedBall (0 : Euc d) R)).toReal with hV
  have hpt : ∀ w, ‖(γ w - γ x) * Q (x - w)‖ ≤ (closedBall x R).indicator (fun _ => C0 * R * B) w := by
    intro w
    by_cases hw : w ∈ closedBall x R
    · rw [indicator_of_mem hw, Real.norm_eq_abs, abs_mul]
      have hu : ‖x - w‖ ≤ R := by
        rw [mem_closedBall, dist_eq_norm, norm_sub_rev] at hw; exact hw
      have h1 := hfar R hR L hL γ hγ x hx hxn (x - w) hu
      rw [show x - (x - w) = w by abel] at h1
      have h2 : |γ w - γ x| ≤ C0 * R := h1.trans (mul_le_mul_of_nonneg_left hu hC0)
      calc |γ w - γ x| * |Q (x - w)| ≤ (C0 * R) * B := mul_le_mul h2 (hB _) (abs_nonneg _) (by positivity)
        _ = _ := by ring
    · rw [indicator_of_notMem hw, Real.norm_eq_abs]
      have : Q (x - w) = 0 := by
        by_contra h
        apply hw
        have := hQs (subset_tsupport Q h)
        rw [mem_closedBall, dist_zero_right] at this
        rw [mem_closedBall, dist_eq_norm, norm_sub_rev]; exact this
      rw [this]; simp
  have hind : Integrable ((closedBall x R).indicator (fun _ => C0 * R * B)) volume :=
    (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const measure_closedBall_lt_top.ne)
  have := norm_integral_le_of_norm_le hind (Filter.Eventually.of_forall hpt)
  rw [Real.norm_eq_abs] at this
  refine this.trans ?_
  rw [integral_indicator measurableSet_closedBall, setIntegral_const]
  simp only [smul_eq_mul]
  rw [Measure.real, Measure.addHaar_closedBall_center]
  nlinarith [mul_nonneg hC0 (by linarith : (0 : ℝ) ≤ R), mul_nonneg hB0 (ENNReal.toReal_nonneg (a := volume (closedBall (0 : Euc d) R)))]

end HRS.MH.AdjointRd.Phase2SA12Construction
