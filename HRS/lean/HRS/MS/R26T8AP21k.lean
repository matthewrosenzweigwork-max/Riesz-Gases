import HRS.MS.R26T8AP21j
import HRS.MS.R26T8AP01b

/-!
# S8.2 local Newton layer, packet T8A.P21 (part k): the mixed jet of the leading source as a Leibniz sum
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_kz_contDiffAt {z : Euc d} (hz : z ≠ 0) : ContDiffAt ℝ ∞ (r26t8a_kz d) z := by
  unfold r26t8a_kz
  exact contDiffAt_const.mul (HRS.contDiffAt_rpow_norm (V := Euc d) (-criticalS d - 2) hz)

theorem r26t8a_kz_jet (d : ℕ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ k, ∀ z : Euc d, z ≠ 0 →
      ‖iteratedFDeriv ℝ i (r26t8a_kz d) z‖ ≤ C * ‖z‖ ^ (-criticalS d - 2 - (i : ℝ)) := by
  choose Ci hCi0 hCi using fun i => HRS.norm_iteratedFDeriv_rpow_norm_le (V := Euc d) (-criticalS d - 2) i
  refine ⟨|-(criticalS d / 2)| * ∑ i ∈ Finset.range (k + 1), Ci i,
    mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun i _ => hCi0 i), fun i hi z hz => ?_⟩
  have h1 : ‖iteratedFDeriv ℝ i (r26t8a_kz d) z‖ = |-(criticalS d / 2)| *
      ‖iteratedFDeriv ℝ i (fun w : Euc d => ‖w‖ ^ (-criticalS d - 2)) z‖ :=
    r26t8a_p02_const_mul (f := fun w : Euc d => ‖w‖ ^ (-criticalS d - 2)) (-(criticalS d / 2))
      (HRS.contDiffAt_rpow_norm (V := Euc d) _ hz) i
  rw [h1]
  have h2 : Ci i ≤ ∑ i ∈ Finset.range (k + 1), Ci i :=
    Finset.single_le_sum (f := Ci) (fun j _ => hCi0 j) (Finset.mem_range.2 (by omega))
  have h3 := hCi i z hz
  have hn : 0 ≤ ‖z‖ ^ (-criticalS d - 2 - (i : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  calc |-(criticalS d / 2)| * ‖iteratedFDeriv ℝ i (fun w : Euc d => ‖w‖ ^ (-criticalS d - 2)) z‖
      ≤ |-(criticalS d / 2)| * (Ci i * ‖z‖ ^ (-criticalS d - 2 - (i : ℝ))) :=
        mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    _ ≤ |-(criticalS d / 2)| * ((∑ i ∈ Finset.range (k + 1), Ci i) * ‖z‖ ^ (-criticalS d - 2 - (i : ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hn) (abs_nonneg _)
    _ = _ := by ring

theorem r26t8a_ktil_contDiff {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {R : ℝ} (hR : 0 < R) :
    ContDiff ℝ ∞ (fun w : Euc d => r26t8a_psiCut chi R w * r26t8a_kz d w) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hpsi := r26t8a_psiCut_contDiff hchi R
  by_cases hx : x = 0
  · have hev : (fun w : Euc d => r26t8a_psiCut chi R w * r26t8a_kz d w) =ᶠ[𝓝 x] fun _ => 0 := by
      have hopen : IsOpen {u : Euc d | ‖u‖ < R / 8} := isOpen_lt continuous_norm continuous_const
      filter_upwards [hopen.mem_nhds (by simp [hx]; positivity)] with u hu
      rw [r26t8a_psiCut_zero hchi hR (le_of_lt (show ‖u‖ < R / 8 from hu)), zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · exact hpsi.contDiffAt.mul (r26t8a_kz_contDiffAt hx)

theorem r26t8a_Q_contDiff {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (N : ℕ) :
    ContDiff ℝ (N : WithTop ℕ∞) (fun Yw : Euc d × Euc d => r26t8a_Q f Yw.1 Yw.2) := by
  have e : (fun Yw : Euc d × Euc d => r26t8a_Q f Yw.1 Yw.2) = fun Yw =>
      (r26t8a_u f Yw.1 Yw.2 (0 + 1) (1 / 2) - r26t8a_u f Yw.1 Yw.2 (0 + 1) (-1 / 2)) -
        r26t8a_u f Yw.1 Yw.2 (0 + 2) 0 := funext fun Yw => r26t8a_Q_eq_u f Yw.1 Yw.2
  rw [e]
  exact ((r26t8a_u_joint_contDiff hf 1 (1 / 2) N).sub (r26t8a_u_joint_contDiff hf 1 (-1 / 2) N)).sub
    (r26t8a_u_joint_contDiff hf 2 0 N)

theorem r26t8a_lead_nest_bound (hd : 1 ≤ d) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {f : Euc d → ℝ}
    (hf : ContDiff ℝ ∞ f) (p q : ℕ) (X z : Euc d) (hz : z ≠ 0) :
    ‖mixedJet p q (r26t8a_lead f) X z‖ ≤ ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i (r26t8a_kz d) z‖ *
        ‖r26t8a_nest p (q - i) (fun Yw : Euc d × Euc d => r26t8a_Q f Yw.1 Yw.2) X z‖ := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  set R : ℝ := 2 * ‖z‖ with hRdef
  have hR : 0 < R := by rw [hRdef]; positivity
  set kt : Euc d → ℝ := fun w => r26t8a_psiCut chi R w * r26t8a_kz d w with hkt
  have hball : ∀ w : Euc d, ‖w - z‖ < ‖z‖ / 2 → ‖z‖ / 2 ≤ ‖w‖ := fun w hw => by
    have := norm_sub_norm_le z w
    rw [norm_sub_rev] at this
    linarith
  have hmid : ∀ (Y w : Euc d), ‖w - z‖ < ‖z‖ / 2 → midPair (r26t8a_lead f) Y w = kt w * r26t8a_Q f Y w := by
    intro Y w hw
    have h1 := hball w hw
    have hw0 : w ≠ 0 := by
      intro h; rw [h, norm_zero] at h1; linarith
    rw [r26t8a_lead_mid hd f Y hw0, hkt]
    simp only [r26t8a_psiCut_one hchi hR (show R / 4 ≤ ‖w‖ by rw [hRdef]; linarith), one_mul]
  have hev : ∀ Y : Euc d, (fun w => midPair (r26t8a_lead f) Y w) =ᶠ[𝓝 z] fun w => kt w * r26t8a_Q f Y w := by
    intro Y
    filter_upwards [Metric.ball_mem_nhds z (half_pos hn)] with w hw
    exact hmid Y w (by rw [Metric.mem_ball, dist_eq_norm] at hw; exact hw)
  have hmix : mixedJet p q (r26t8a_lead f) X z =
      r26t8a_nest p q (fun Yw : Euc d × Euc d => kt Yw.2 * r26t8a_Q f Yw.1 Yw.2) X z := by
    unfold mixedJet r26t8a_nest
    congr 1
    funext Y
    exact ((hev Y).iteratedFDeriv ℝ q).eq_of_nhds
  have hktd : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) kt :=
    (r26t8a_ktil_contDiff hchi hR).of_le (by exact_mod_cast le_top)
  have hjet : ∀ i : ℕ, iteratedFDeriv ℝ i kt z = iteratedFDeriv ℝ i (r26t8a_kz d) z := fun i => by
    have : kt =ᶠ[𝓝 z] r26t8a_kz d := by
      filter_upwards [Metric.ball_mem_nhds z (half_pos hn)] with w hw
      have hw' : ‖w - z‖ < ‖z‖ / 2 := by rw [Metric.mem_ball, dist_eq_norm] at hw; exact hw
      simp only [hkt, r26t8a_psiCut_one hchi hR (show R / 4 ≤ ‖w‖ by rw [hRdef]; linarith [hball w hw']), one_mul]
    exact (this.iteratedFDeriv ℝ i).eq_of_nhds
  rw [hmix]
  refine (r26t8a_nest_product_bound p q kt _ X z hktd (r26t8a_Q_contDiff hf (p + q))).trans ?_
  refine le_of_eq (Finset.sum_congr rfl fun i _ => ?_)
  rw [hjet]

end HRS.MS.R26T8A
