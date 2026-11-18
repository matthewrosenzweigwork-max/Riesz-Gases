import HRS.MS.S82UA3

/-!
# S8.2 A01 (S82U): the grouped edge bound
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82U
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2 HRS.MS.S82T

/-- The triple weight `⟨u⟩^{2M} ⟨v⟩^{2M} ⟨w⟩^{2M}`. -/
def uW {d : ℕ} (M : ℝ) (u v w : Euc d) : ℝ := jbracket u ^ (2 * M) * jbracket v ^ (2 * M) * jbracket w ^ (2 * M)

lemma u_jb_le_two {d : ℕ} {M : ℝ} (hM : 0 ≤ M) (x : Euc d) : jbracket x ^ M ≤ jbracket x ^ (2 * M) :=
  Real.rpow_le_rpow_of_exponent_le (u_jb_ge_one x) (by linarith)

lemma u_wt1 {d : ℕ} {M : ℝ} (hM : 0 ≤ M) (u v w : Euc d) :
    jbracket u ^ M * jbracket w ^ M ≤ uW M u v w ∧ jbracket v ^ M * jbracket w ^ M ≤ uW M u v w ∧
    jbracket u ^ M * jbracket v ^ M ≤ uW M u v w ∧
    jbracket u ^ M * jbracket w ^ (2 * M) ≤ uW M u v w ∧
    jbracket v ^ M * jbracket w ^ (2 * M) ≤ uW M u v w ∧ 1 ≤ uW M u v w := by
  have hu := u_jb_le_two hM u
  have hv := u_jb_le_two hM v
  have hw := u_jb_le_two hM w
  have gu := u_jb_rpow_ge_one (by linarith : 0 ≤ 2 * M) u
  have gv := u_jb_rpow_ge_one (by linarith : 0 ≤ 2 * M) v
  have gw := u_jb_rpow_ge_one (by linarith : 0 ≤ 2 * M) w
  have pu := u_jb_rpow_pos M u
  have pv := u_jb_rpow_pos M v
  have pw := u_jb_rpow_pos M w
  unfold uW
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc _ ≤ jbracket u ^ (2 * M) * jbracket w ^ (2 * M) := mul_le_mul hu hw pw.le (by linarith)
      _ ≤ _ := by nlinarith [mul_pos (by linarith : (0:ℝ) < jbracket u ^ (2 * M)) (by linarith : (0:ℝ) < jbracket w ^ (2 * M))]
  · calc _ ≤ jbracket v ^ (2 * M) * jbracket w ^ (2 * M) := mul_le_mul hv hw pw.le (by linarith)
      _ ≤ _ := by nlinarith [mul_pos (by linarith : (0:ℝ) < jbracket v ^ (2 * M)) (by linarith : (0:ℝ) < jbracket w ^ (2 * M))]
  · calc _ ≤ jbracket u ^ (2 * M) * jbracket v ^ (2 * M) := mul_le_mul hu hv pv.le (by linarith)
      _ ≤ _ := by nlinarith [mul_pos (by linarith : (0:ℝ) < jbracket u ^ (2 * M)) (by linarith : (0:ℝ) < jbracket v ^ (2 * M))]
  · calc _ ≤ jbracket u ^ (2 * M) * jbracket w ^ (2 * M) := mul_le_mul hu le_rfl (by linarith) (by linarith)
      _ ≤ _ := by nlinarith [mul_pos (by linarith : (0:ℝ) < jbracket u ^ (2 * M)) (by linarith : (0:ℝ) < jbracket w ^ (2 * M))]
  · calc _ ≤ jbracket v ^ (2 * M) * jbracket w ^ (2 * M) := mul_le_mul hv le_rfl (by linarith) (by linarith)
      _ ≤ _ := by nlinarith [mul_pos (by linarith : (0:ℝ) < jbracket v ^ (2 * M)) (by linarith : (0:ℝ) < jbracket w ^ (2 * M))]
  · nlinarith [mul_pos (by linarith : (0:ℝ) < jbracket u ^ (2 * M)) (by linarith : (0:ℝ) < jbracket v ^ (2 * M))]

lemma u_pole_pos {d : ℕ} (x y : Euc d) : 1 ≤ pole x y := s82q_pole_ge_one x y

lemma u_pole_symm {d : ℕ} (x y : Euc d) : pole x y = pole y x := by
  unfold pole smallRadius; rw [norm_sub_rev]

/-- Grouped edge estimate (norm form). -/
theorem u_edge_norm {d : ℕ} (hd : 2 ≤ d) {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A) (hQ : PairCorrector a beta rho M A f Q)
    {u v w : Euc d} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ‖rieszKernelGrad d (criticalS d) (u - v)‖ * ‖s82p2_gt Q u w - s82p2_gt Q v w‖ ≤
      HRS.Whole.movtr_sigma (criticalS d) * (2 ^ M * 2 ^ criticalS d + 6) *
        (A * uW M u v w * (pole u v * (pole u w + pole v w))) := by
  have hs1 : 1 ≤ criticalS d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    unfold criticalS; linarith
  have hs0 : 0 ≤ criticalS d := by linarith
  have hσ := s82t_sigma_nonneg (criticalS d) hs0
  have hz : u - v ≠ 0 := sub_ne_zero.2 huv
  have ha : 0 < ‖u - v‖ := norm_pos_iff.2 hz
  have hGn : ‖rieszKernelGrad d (criticalS d) (u - v)‖ =
      HRS.Whole.movtr_sigma (criticalS d) * ‖u - v‖ ^ (-criticalS d - 1) :=
    HRS.Whole.movtr_rieszKernelGrad_norm (criticalS d) hs0 hz
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := u_wt1 hM u v w
  have hpuv := u_pole_pos u v
  have hpuw := u_pole_pos u w
  have hpvw := u_pole_pos v w
  have hW0 : 0 ≤ uW M u v w := by linarith
  have hAW : 0 ≤ A * uW M u v w := mul_nonneg hA hW0
  have hpp : 0 ≤ pole u v * (pole u w + pole v w) := by positivity
  have hC : (0 : ℝ) ≤ 2 ^ M * 2 ^ criticalS d := by positivity
  rw [hGn]
  by_cases hcase : 2 * ‖u - v‖ < ‖u - w‖
  · -- near case
    have hnear := u_gtdiff_near hM hA hQ u v w hcase
    have ha' : ‖u - v‖ ^ (-criticalS d - 1) * ‖u - v‖ = ‖u - v‖ ^ (-criticalS d) := by
      rw [show -criticalS d - 1 = -criticalS d + -1 by ring, Real.rpow_add ha, Real.rpow_neg_one,
        inv_mul_cancel_right₀ ha.ne']
    have hpow : ‖u - v‖ ^ (-criticalS d) ≤ pole u v := by
      have := u_rpow_neg_le_min hs0 ha
      unfold pole smallRadius; linarith
    set Bv := A * (2 ^ M * 2 ^ criticalS d) * (jbracket u ^ M * jbracket w ^ (2 * M)) * pole u w with hBv
    calc HRS.Whole.movtr_sigma (criticalS d) * ‖u - v‖ ^ (-criticalS d - 1) *
          ‖s82p2_gt Q u w - s82p2_gt Q v w‖
        ≤ HRS.Whole.movtr_sigma (criticalS d) * ‖u - v‖ ^ (-criticalS d - 1) * (‖u - v‖ * Bv) :=
          mul_le_mul_of_nonneg_left hnear (mul_nonneg hσ (Real.rpow_nonneg ha.le _))
      _ = HRS.Whole.movtr_sigma (criticalS d) * ‖u - v‖ ^ (-criticalS d) * Bv := by
          rw [← ha']; ring
      _ ≤ HRS.Whole.movtr_sigma (criticalS d) * pole u v * Bv := by
          have hBv0 : 0 ≤ Bv := by
            rw [hBv]
            exact mul_nonneg (mul_nonneg (mul_nonneg hA hC) (mul_nonneg (u_jb_rpow_pos M u).le
              (u_jb_rpow_pos _ w).le)) (by linarith)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hσ) hBv0
      _ ≤ _ := by
          rw [hBv]
          have h1 : A * (2 ^ M * 2 ^ criticalS d) * (jbracket u ^ M * jbracket w ^ (2 * M)) ≤
              A * (2 ^ M * 2 ^ criticalS d) * uW M u v w :=
            mul_le_mul_of_nonneg_left w4 (mul_nonneg hA hC)
          have h2 : A * (2 ^ M * 2 ^ criticalS d) * uW M u v w =
              (2 ^ M * 2 ^ criticalS d) * (A * uW M u v w) := by ring
          have h3 : 0 ≤ (2 ^ M * 2 ^ criticalS d) * (A * uW M u v w) := mul_nonneg hC hAW
          calc HRS.Whole.movtr_sigma (criticalS d) * pole u v *
                (A * (2 ^ M * 2 ^ criticalS d) * (jbracket u ^ M * jbracket w ^ (2 * M)) * pole u w)
              ≤ HRS.Whole.movtr_sigma (criticalS d) * pole u v *
                ((2 ^ M * 2 ^ criticalS d) * (A * uW M u v w) * pole u w) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (h1.trans_eq h2)
                  (by linarith)) (mul_nonneg hσ (by linarith))
            _ ≤ HRS.Whole.movtr_sigma (criticalS d) * pole u v *
                ((2 ^ M * 2 ^ criticalS d) * (A * uW M u v w) * (pole u w + pole v w)) := by
                gcongr
                linarith
            _ ≤ _ := by
                have : 0 ≤ A * uW M u v w * (pole u v * (pole u w + pole v w)) := mul_nonneg hAW hpp
                nlinarith [mul_nonneg hσ this]
  · -- far case
    rw [not_lt] at hcase
    have hb : 0 < ‖u - w‖ := norm_pos_iff.2 (sub_ne_zero.2 huw)
    have hc : 0 < ‖v - w‖ := norm_pos_iff.2 (sub_ne_zero.2 hvw)
    have hdel : ‖s82p2_gt Q u w - s82p2_gt Q v w‖ ≤ ‖s82p2_gt Q u w‖ + ‖s82p2_gt Q v w‖ := norm_sub_le _ _
    have g1 := s82p2_gt_norm_le hQ u w huw
    have g2 := s82p2_gt_norm_le hQ v w hvw
    have hsb := u_scalar (s := criticalS d) (a := ‖u - v‖) (b := ‖u - w‖) (κ := 3) hs1 ha hb
      (by norm_num) (by linarith)
    have hsc := u_scalar (s := criticalS d) (a := ‖u - v‖) (b := ‖v - w‖) (κ := 3) hs1 ha hc
      (by norm_num) (by
        have : ‖v - w‖ ≤ ‖v - u‖ + ‖u - w‖ := by simpa using norm_sub_le_norm_sub_add_norm_sub v u w
        rw [norm_sub_rev v u] at this
        linarith)
    have hpow : ‖u - v‖ ^ (-criticalS d - 1) = ‖u - v‖ ^ (-criticalS d - 1) := rfl
    have e_pole_uv : pole u v = 1 + (min 1 ‖u - v‖) ^ (-criticalS d) := rfl
    have e_pole_uw : pole u w = 1 + (min 1 ‖u - w‖) ^ (-criticalS d) := rfl
    have e_pole_vw : pole v w = 1 + (min 1 ‖v - w‖) ^ (-criticalS d) := rfl
    have e_rb : smallRadius u w = min 1 ‖u - w‖ := rfl
    have e_rc : smallRadius v w = min 1 ‖v - w‖ := rfl
    rw [e_rb] at g1
    rw [e_rc] at g2
    rw [← e_pole_uv, ← e_pole_uw] at hsb
    rw [← e_pole_uv, ← e_pole_vw] at hsc
    set P := ‖u - v‖ ^ (-criticalS d - 1) with hP
    have hP0 : 0 ≤ P := Real.rpow_nonneg ha.le _
    have hpw1 : Phase2S82.pairWeight M u w ≤ uW M u v w := w1
    have hpw2 : Phase2S82.pairWeight M v w ≤ uW M u v w := w2
    have k1 : P * ‖s82p2_gt Q u w‖ ≤ 6 * (A * uW M u v w * (pole u v * pole u w)) := by
      calc P * ‖s82p2_gt Q u w‖ ≤ P * (A * Phase2S82.pairWeight M u w * (1 + (min 1 ‖u - w‖) ^ (1 - criticalS d))) :=
            mul_le_mul_of_nonneg_left g1 hP0
        _ ≤ P * (A * uW M u v w * (1 + (min 1 ‖u - w‖) ^ (1 - criticalS d))) := by
            gcongr
        _ = A * uW M u v w * (P * (1 + (min 1 ‖u - w‖) ^ (1 - criticalS d))) := by ring
        _ ≤ A * uW M u v w * (2 * 3 * (pole u v * pole u w)) := mul_le_mul_of_nonneg_left hsb hAW
        _ = 6 * (A * uW M u v w * (pole u v * pole u w)) := by ring
    have k2 : P * ‖s82p2_gt Q v w‖ ≤ 6 * (A * uW M u v w * (pole u v * pole v w)) := by
      calc P * ‖s82p2_gt Q v w‖ ≤ P * (A * Phase2S82.pairWeight M v w * (1 + (min 1 ‖v - w‖) ^ (1 - criticalS d))) :=
            mul_le_mul_of_nonneg_left g2 hP0
        _ ≤ P * (A * uW M u v w * (1 + (min 1 ‖v - w‖) ^ (1 - criticalS d))) := by
            gcongr
        _ = A * uW M u v w * (P * (1 + (min 1 ‖v - w‖) ^ (1 - criticalS d))) := by ring
        _ ≤ A * uW M u v w * (2 * 3 * (pole u v * pole v w)) := mul_le_mul_of_nonneg_left hsc hAW
        _ = 6 * (A * uW M u v w * (pole u v * pole v w)) := by ring
    calc HRS.Whole.movtr_sigma (criticalS d) * P * ‖s82p2_gt Q u w - s82p2_gt Q v w‖
        ≤ HRS.Whole.movtr_sigma (criticalS d) * (P * (‖s82p2_gt Q u w‖ + ‖s82p2_gt Q v w‖)) := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left hdel (mul_nonneg hσ hP0)
      _ ≤ HRS.Whole.movtr_sigma (criticalS d) *
            (6 * (A * uW M u v w * (pole u v * pole u w)) + 6 * (A * uW M u v w * (pole u v * pole v w))) := by
          gcongr
          rw [mul_add]; linarith
      _ = HRS.Whole.movtr_sigma (criticalS d) * 6 * (A * uW M u v w * (pole u v * (pole u w + pole v w))) := by ring
      _ ≤ _ := by
          have : 0 ≤ A * uW M u v w * (pole u v * (pole u w + pole v w)) := mul_nonneg hAW hpp
          nlinarith [mul_nonneg hσ this, mul_nonneg hσ (mul_nonneg hC this)]

/-- Grouped edge estimate. -/
theorem u_edge_bound {d : ℕ} (hd : 2 ≤ d) {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A) (hQ : PairCorrector a beta rho M A f Q)
    {u v w : Euc d} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    |inner ℝ (rieszKernelGrad d (criticalS d) (u - v)) (s82p2_gt Q u w - s82p2_gt Q v w)| ≤
      HRS.Whole.movtr_sigma (criticalS d) * (2 ^ M * 2 ^ criticalS d + 6) *
        (A * uW M u v w * (pole u v * (pole u w + pole v w))) :=
  (abs_real_inner_le_norm _ _).trans (u_edge_norm hd hM hA hQ huv huw hvw)

end HRS.MS.S82U
