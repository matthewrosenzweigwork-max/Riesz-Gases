import HRS.MS.S82P2Grad7

/-!
# S8.2 (S82P2): pointwise ingredients for the centering of `∇_x Q`
Segment (mean value) bound for the corrector away from the diagonal and the pointwise slope limit.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

lemma s82p2_jb_add_le {d : ℕ} (x u : Euc d) : jbracket (x + u) ≤ jbracket x + ‖u‖ := by
  have hx := HRS.MS.S82N.s82n_jb_pos x
  have hxsq := HRS.MS.S82N.s82n_jb_sq x
  have hysq := HRS.MS.S82N.s82n_jb_sq (x + u)
  have hy := HRS.MS.S82N.s82n_jb_pos (x + u)
  have hnorm : ‖x + u‖ ≤ ‖x‖ + ‖u‖ := norm_add_le _ _
  have hxn : ‖x‖ ≤ jbracket x := by
    unfold jbracket
    exact (le_abs_self _).trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg ‖x‖]))
  have h1 : ‖x + u‖ ^ 2 ≤ (‖x‖ + ‖u‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have h2 : ‖x‖ * ‖u‖ ≤ jbracket x * ‖u‖ := mul_le_mul_of_nonneg_right hxn (norm_nonneg u)
  have : jbracket (x + u) ^ 2 ≤ (jbracket x + ‖u‖) ^ 2 := by
    rw [hysq]; nlinarith
  exact (pow_le_pow_iff_left₀ hy.le (by positivity) two_ne_zero).1 this

/-- Mean value bound for the corrector along the segment `[x, x + t v]` away from the pole `z`. -/
lemma s82p2_Q_segment {d : ℕ} (hd : 2 ≤ d) {a beta M A : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A)
    {rho : Euc d → ℝ} {f : Euc d → ℝ} {Q : Euc d → Euc d → ℝ}
    (hQ : PairCorrector a beta rho M A f Q) (x z v : Euc d) (hv : ‖v‖ = 1) {t : ℝ}
    (ht0 : 0 < |t|) (ht1 : |t| ≤ 1) (hz : 2 * |t| ≤ ‖z - x‖) :
    |Q (x + t • v) z - Q x z| ≤ |t| * (A * ((2 * jbracket x) ^ M * jbracket z ^ M) *
      (1 + 2 ^ (criticalS d - 1) * smallRadius x z ^ (1 - criticalS d))) := by
  have hs1 : 1 ≤ criticalS d := by
    unfold criticalS
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hjx := HRS.MS.S82N.s82n_jb_one_le x
  have hjxpos := HRS.MS.S82N.s82n_jb_pos x
  set C : ℝ := A * ((2 * jbracket x) ^ M * jbracket z ^ M) *
    (1 + 2 ^ (criticalS d - 1) * smallRadius x z ^ (1 - criticalS d)) with hC
  have hrx : 0 < smallRadius x z :=
    lt_min one_pos (norm_pos_iff.2 (sub_ne_zero.2 (fun h => by
      have : ‖z - x‖ = 0 := by rw [h]; simp
      linarith)))
  have hball : Convex ℝ (Metric.closedBall x (|t|)) := convex_closedBall _ _
  have hmem : ∀ y ∈ Metric.closedBall x (|t|), y ≠ z ∧
      ‖fderiv ℝ (fun y' => Q y' z) y‖ ≤ C := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm] at hy
    have hyz : ‖z - x‖ / 2 ≤ ‖y - z‖ := by
      have h3 : ‖z - x‖ ≤ ‖z - y‖ + ‖y - x‖ := by
        simpa using norm_sub_le_norm_sub_add_norm_sub z y x
      rw [norm_sub_rev y z]; linarith
    have hyne : y ≠ z := by
      intro h
      rw [h, sub_self, norm_zero] at hyz
      linarith
    refine ⟨hyne, ?_⟩
    have hnorm : ‖fderiv ℝ (fun y' => Q y' z) y‖ = ‖Phase2S82.pairGradX Q y z‖ := by
      unfold Phase2S82.pairGradX gradient
      exact ((InnerProductSpace.toDual ℝ (Euc d)).symm.norm_map _).symm
    rw [hnorm]
    have hg := hQ.gradient y z hyne
    have hg' : ‖Phase2S82.pairGradX Q y z‖ ≤ A * pairWeight M y z *
        (1 + smallRadius y z ^ (1 - criticalS d)) := by
      have := norm_nonneg (Phase2S82.pairGradY Q y z)
      linarith
    refine hg'.trans ?_
    have hjy : jbracket y ≤ 2 * jbracket x := by
      have h1 := s82p2_jb_add_le x (y - x)
      rw [add_sub_cancel] at h1
      have : ‖y - x‖ ≤ 1 := hy.trans ht1
      linarith
    have hpw : pairWeight M y z ≤ (2 * jbracket x) ^ M * jbracket z ^ M := by
      unfold pairWeight
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (HRS.MS.S82N.s82n_jb_pos y).le hjy hM)
        (s82p2_jb_rpow_nonneg M z)
    have hry : smallRadius x z / 2 ≤ smallRadius y z := by
      unfold smallRadius
      have hxz : ‖x - z‖ = ‖z - x‖ := norm_sub_rev _ _
      rw [hxz]
      refine le_min ?_ ?_
      · have := min_le_left (1 : ℝ) ‖z - x‖; linarith [min_le_left (1 : ℝ) ‖z - x‖, hyz]
      · have := min_le_right (1 : ℝ) ‖z - x‖; linarith
    have hpow : smallRadius y z ^ (1 - criticalS d) ≤
        2 ^ (criticalS d - 1) * smallRadius x z ^ (1 - criticalS d) := by
      calc smallRadius y z ^ (1 - criticalS d)
          ≤ (smallRadius x z / 2) ^ (1 - criticalS d) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hry (by linarith)
        _ = 2 ^ (criticalS d - 1) * smallRadius x z ^ (1 - criticalS d) := by
            rw [Real.div_rpow hrx.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num)]
            ring_nf
    have hApw : 0 ≤ A := hA
    rw [hC]
    have hjz0 := s82p2_jb_rpow_nonneg M z
    have hry0 : 0 ≤ smallRadius y z := le_min zero_le_one (norm_nonneg _)
    have hb0 : 0 ≤ A * ((2 * jbracket x) ^ M * jbracket z ^ M) :=
      mul_nonneg hA (mul_nonneg (Real.rpow_nonneg (by linarith) _) hjz0)
    have hr0' := Real.rpow_nonneg hry0 (1 - criticalS d)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpw hA) (by linarith) (by linarith) hb0
  have hdiff : ∀ y ∈ Metric.closedBall x (|t|), DifferentiableAt ℝ (fun y' => Q y' z) y :=
    fun y hy => s82p2_Q_diff hQ y z (hmem y hy).1
  have hxm : x ∈ Metric.closedBall x (|t|) := Metric.mem_closedBall_self (abs_nonneg t)
  have hxtm : x + t • v ∈ Metric.closedBall x (|t|) := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hv, mul_one,
      Real.norm_eq_abs]
  have hmv := hball.norm_image_sub_le_of_norm_fderiv_le hdiff (fun y hy => (hmem y hy).2) hxm hxtm
  rw [Real.norm_eq_abs, add_sub_cancel_left, norm_smul, hv, mul_one, Real.norm_eq_abs] at hmv
  rw [mul_comm]
  exact hmv

/-- pointwise slope limit of the corrector in the direction `v`. -/
lemma s82p2_slope_tendsto {d : ℕ} {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) (x z v : Euc d)
    (hxz : x ≠ z) :
    Tendsto (fun t : ℝ => t⁻¹ * (Q (x + t • v) z - Q x z)) (𝓝[≠] 0)
      (𝓝 (inner ℝ (s82p2_gt Q x z) v)) := by
  have hdiff := s82p2_Q_diff hQ x z hxz
  have h1 : HasDerivAt (fun s : ℝ => x + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have h2 : HasFDerivAt (fun y : Euc d => Q y z) (fderiv ℝ (fun y => Q y z) x) (x + (0 : ℝ) • v) := by
    simpa using hdiff.hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
  have h4 := h3.tendsto_slope_zero
  have e : fderiv ℝ (fun y => Q y z) x v = inner ℝ (s82p2_gt Q x z) v := by
    rw [s82p2_gt_eq hQ x z hxz]
    unfold Phase2S82.pairGradX
    rw [inner_gradient_left]
  simp only [Function.comp_def, zero_add, smul_zero, add_zero] at h4
  rw [e] at h4
  refine h4.congr fun t => ?_
  simp [smul_eq_mul]

end HRS.MS.S82P2
