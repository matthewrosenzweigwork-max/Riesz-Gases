import HRS.MS.S82UA2

/-!
# S8.2 A01 (S82U): gradient difference near the diagonal, and the grouped edge bound
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82U
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2 HRS.MS.S82T

lemma u_gt_unfold {d : ℕ} (Q : Euc d → Euc d → ℝ) {x w : Euc d} (h : x ≠ w) :
    s82p2_gt Q x w = (InnerProductSpace.toDual ℝ (Euc d)).symm
      ((fderiv ℝ (Function.uncurry Q) (x, w)).comp (ContinuousLinearMap.inl ℝ (Euc d) (Euc d))) := by
  unfold s82p2_gt; rw [if_pos h]

lemma u_jb_mul_le {d : ℕ} (u w : Euc d) : jbracket u * jbracket w ≥ jbracket u ∧
    jbracket u * jbracket w ≥ jbracket w := by
  have h1 := u_jb_ge_one u
  have h2 := u_jb_ge_one w
  constructor <;> nlinarith

lemma u_gtdiff_near {d : ℕ} {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A) (hQ : PairCorrector a beta rho M A f Q)
    (u v w : Euc d) (h : 2 * ‖u - v‖ < ‖u - w‖) :
    ‖s82p2_gt Q u w - s82p2_gt Q v w‖ ≤ ‖u - v‖ *
      (A * (2 ^ M * 2 ^ criticalS d) * (jbracket u ^ M * jbracket w ^ (2 * M)) * pole u w) := by
  have hs0 : 0 ≤ criticalS d := by unfold criticalS; positivity
  have hb : 0 < ‖u - w‖ := lt_of_le_of_lt (by positivity) h
  have huw : u ≠ w := fun e => by rw [e, sub_self, norm_zero] at hb; exact lt_irrefl _ hb
  have hnuv : 0 ≤ ‖u - v‖ := norm_nonneg _
  have hpne : ∀ p ∈ Metric.closedBall u ‖u - v‖, p ≠ w := by
    intro p hp e
    rw [Metric.mem_closedBall, dist_eq_norm] at hp
    rw [e] at hp
    have : ‖u - w‖ ≤ ‖w - u‖ := by rw [norm_sub_rev]
    rw [norm_sub_rev] at hp
    linarith
  have hvw : v ≠ w := by
    apply hpne v
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
  have hrad : ∀ p ∈ Metric.closedBall u ‖u - v‖, ‖p - w‖ ≥ ‖u - w‖ / 2 := by
    intro p hp
    rw [Metric.mem_closedBall, dist_eq_norm] at hp
    have h3 : ‖u - w‖ ≤ ‖u - p‖ + ‖p - w‖ := by simpa using norm_sub_le_norm_sub_add_norm_sub u p w
    rw [norm_sub_rev u p] at h3
    linarith
  set Bv : ℝ := A * (2 ^ M * 2 ^ criticalS d) * (jbracket u ^ M * jbracket w ^ (2 * M)) * pole u w with hBv
  have hΦ : ContDiffOn ℝ 2 (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    hQ.smooth.of_le (by norm_num)
  have hB : ∀ p ∈ Metric.closedBall u ‖u - v‖,
      ‖iteratedFDeriv ℝ 2 (Function.uncurry Q) (p, w)‖ ≤ Bv := by
    intro p hp
    have hH := hQ.hessian p w (hpne p hp)
    refine hH.trans ?_
    have hpu : ‖p - u‖ ≤ ‖u - v‖ := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hp; exact hp
    -- weight
    have hjp : jbracket p ≤ 2 * (jbracket u * jbracket w) := by
      have h1 := s82p2_jb_add_le u (p - u)
      rw [add_sub_cancel] at h1
      have h2 : ‖u - w‖ ≤ jbracket u + jbracket w := by
        have a1 : ‖u‖ ≤ jbracket u := by
          unfold jbracket
          exact (le_abs_self _).trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg ‖u‖]))
        have a2 : ‖w‖ ≤ jbracket w := by
          unfold jbracket
          exact (le_abs_self _).trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg ‖w‖]))
        exact (norm_sub_le _ _).trans (by linarith)
      obtain ⟨m1, m2⟩ := u_jb_mul_le u w
      linarith
    have hpw : Phase2S82.pairWeight M p w ≤ 2 ^ M * (jbracket u ^ M * jbracket w ^ (2 * M)) := by
      unfold Phase2S82.pairWeight
      have h1 : jbracket p ^ M ≤ (2 * (jbracket u * jbracket w)) ^ M :=
        Real.rpow_le_rpow (HRS.MS.S82N.s82n_jb_pos p).le hjp hM
      have h2 : (2 * (jbracket u * jbracket w)) ^ M = 2 ^ M * (jbracket u ^ M * jbracket w ^ M) := by
        rw [Real.mul_rpow (by norm_num) (mul_nonneg (HRS.MS.S82N.s82n_jb_pos u).le (HRS.MS.S82N.s82n_jb_pos w).le), Real.mul_rpow (HRS.MS.S82N.s82n_jb_pos u).le
          (HRS.MS.S82N.s82n_jb_pos w).le]
      have h3 : jbracket w ^ (2 * M) = jbracket w ^ M * jbracket w ^ M := by
        rw [two_mul, Real.rpow_add (HRS.MS.S82N.s82n_jb_pos w)]
      have h4 : 0 ≤ jbracket w ^ M := (u_jb_rpow_pos M w).le
      calc jbracket p ^ M * jbracket w ^ M ≤ (2 ^ M * (jbracket u ^ M * jbracket w ^ M)) * jbracket w ^ M := by
            rw [← h2]; exact mul_le_mul_of_nonneg_right h1 h4
        _ = 2 ^ M * (jbracket u ^ M * jbracket w ^ (2 * M)) := by rw [h3]; ring
    -- radius
    have hrp : smallRadius u w / 2 ≤ smallRadius p w := by
      unfold smallRadius
      refine le_min ?_ ?_
      · have := min_le_left (1 : ℝ) ‖u - w‖; linarith [min_le_left (1 : ℝ) ‖u - w‖]
      · have := min_le_right (1 : ℝ) ‖u - w‖
        have := hrad p hp
        linarith
    have hr0 : 0 < smallRadius u w := u_min_pos hb
    have hpow : smallRadius p w ^ (-criticalS d) ≤ 2 ^ criticalS d * smallRadius u w ^ (-criticalS d) := by
      calc smallRadius p w ^ (-criticalS d) ≤ (smallRadius u w / 2) ^ (-criticalS d) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hrp (by linarith)
        _ = 2 ^ criticalS d * smallRadius u w ^ (-criticalS d) := by
            rw [Real.div_rpow hr0.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
            ring_nf
    have hpole : 1 + smallRadius p w ^ (-criticalS d) ≤ 2 ^ criticalS d * pole u w := by
      unfold pole
      have h2s : (1 : ℝ) ≤ 2 ^ criticalS d := Real.one_le_rpow (by norm_num) hs0
      nlinarith [Real.rpow_nonneg hr0.le (-criticalS d)]
    have hrp0 : 0 ≤ smallRadius p w ^ (-criticalS d) := by
      unfold smallRadius
      exact Real.rpow_nonneg (le_min zero_le_one (norm_nonneg _)) _
    have hpw0 : 0 ≤ Phase2S82.pairWeight M p w := by
      unfold Phase2S82.pairWeight
      exact mul_nonneg (u_jb_rpow_pos M p).le (u_jb_rpow_pos M w).le
    calc A * Phase2S82.pairWeight M p w * (1 + smallRadius p w ^ (-criticalS d))
        ≤ A * (2 ^ M * (jbracket u ^ M * jbracket w ^ (2 * M))) * (2 ^ criticalS d * pole u w) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hpw hA) hpole
            (by linarith [hrp0])
            (mul_nonneg hA (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
              (mul_nonneg (u_jb_rpow_pos M u).le (u_jb_rpow_pos _ w).le)))
      _ = Bv := by rw [hBv]; ring
  have key := u_grad_lip (Function.uncurry Q) hΦ u v w Bv hpne hB
  rw [u_gt_unfold Q huw, u_gt_unfold Q hvw]
  linarith [key, mul_comm Bv ‖u - v‖]

end HRS.MS.S82U
