import HRS.MS.MfeConfAux183

/-!
# S.B.1 (SB5), R1 (part 1): the master estimate for the difference of two cancellation-convention convolutions

If two kernels `κ₁, κ₂` with `|κ_i(z)| ≤ σ_i |z|^{-s-1}` agree outside the ball of radius `r ≤ 1`, then for `φ` with
`|φ|, ‖Dφ‖ ≤ b (1+|y|)^{-(d+3)}`:
`|rgT κ₁ φ x - rgT κ₂ φ x| ≤ (σ₁+σ₂) · 4·2^{d+3} · b · (1+|x|)^{-(d+3)} · ∫_{|z|≤r} |z|^{-s} dz`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.RdGen
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d : ℕ}

/-- `∫_{|z| ≤ r} |z|^{-s} dz` -/
def sb1eta (d : ℕ) (s r : ℝ) : ℝ := ∫ z in Metric.closedBall (0 : Euc d) r, ‖z‖ ^ (-s)

theorem sb1w_ball_le {p : ℝ} (hp : 0 ≤ p) {x y : Euc d} (h : ‖y - x‖ ≤ 1) :
    sb1w p y ≤ 2 ^ p * sb1w p x := by
  unfold sb1w
  have h1 : (1 + ‖x‖) / 2 ≤ 1 + ‖y‖ := by
    have : ‖x‖ ≤ ‖y‖ + ‖y - x‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub x y 0
      calc ‖x‖ = ‖x - 0‖ := by simp
        _ ≤ ‖x - y‖ + ‖y - 0‖ := this
        _ = ‖y - x‖ + ‖y‖ := by rw [norm_sub_rev, sub_zero]
        _ = ‖y‖ + ‖y - x‖ := add_comm _ _
    linarith [norm_nonneg y]
  have h2 : (0 : ℝ) < (1 + ‖x‖) / 2 := by positivity
  calc (1 + ‖y‖) ^ (-p) ≤ ((1 + ‖x‖) / 2) ^ (-p) :=
        Real.rpow_le_rpow_of_nonpos h2 h1 (by linarith)
    _ = 2 ^ p * (1 + ‖x‖) ^ (-p) := by
        rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        field_simp

/-- pointwise bound of the cancellation integrand -/
theorem sb1_rgR_bound {φ : Euc d → ℝ} (hφd : Differentiable ℝ φ) {b : ℝ}
    (h0 : ∀ y, |φ y| ≤ b * sb1w ((d : ℝ) + 3) y) (h1 : ∀ y, ‖fderiv ℝ φ y‖ ≤ b * sb1w ((d : ℝ) + 3) y)
    (x z : Euc d) (hz : ‖z‖ ≤ 1) :
    |rgR φ x z| ≤ (4 * 2 ^ ((d : ℝ) + 3)) * b * ‖z‖ * sb1w ((d : ℝ) + 3) x := by
  have hb : 0 ≤ b := by
    have := (abs_nonneg (φ 0)).trans (h0 0)
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos hneg (sb1w_pos ((d : ℝ) + 3) (0 : Euc d))
    linarith
  have hp : (0 : ℝ) ≤ (d : ℝ) + 3 := by positivity
  have hwx := sb1w_pos ((d : ℝ) + 3) x
  have h2p : (1 : ℝ) ≤ 2 ^ ((d : ℝ) + 3) := Real.one_le_rpow (by norm_num) hp
  have hz0 := norm_nonneg z
  unfold rgR
  split_ifs with hsmall
  · -- mean value on the ball of radius 1 around x
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := φ) (C := b * (2 ^ ((d : ℝ) + 3) * sb1w ((d : ℝ) + 3) x))
      (s := Metric.closedBall x 1) (x := x) (y := x - z) (fun y _ => hφd y)
      (fun y hy => (h1 y).trans (mul_le_mul_of_nonneg_left (sb1w_ball_le hp (by simpa [dist_eq_norm] using hy)) hb))
      (convex_closedBall x 1) (Metric.mem_closedBall_self zero_le_one)
      (by simpa [dist_eq_norm] using hz)
    have e : ‖x - z - x‖ = ‖z‖ := by simp
    rw [e] at hmv
    rw [Real.norm_eq_abs] at hmv
    refine hmv.trans ?_
    have : 0 ≤ b * (2 ^ ((d : ℝ) + 3) * sb1w ((d : ℝ) + 3) x) * ‖z‖ := by positivity
    nlinarith [mul_nonneg (mul_nonneg hb hwx.le) hz0, mul_nonneg (mul_nonneg (mul_nonneg hb hwx.le) hz0) (sub_nonneg.2 h2p)]
  · push Not at hsmall
    have hw := sb1w_ball_le hp (x := x) (y := x - z) (by simpa using hz)
    calc |φ (x - z)| ≤ b * sb1w ((d : ℝ) + 3) (x - z) := h0 _
      _ ≤ b * (2 ^ ((d : ℝ) + 3) * sb1w ((d : ℝ) + 3) x) := mul_le_mul_of_nonneg_left hw hb
      _ ≤ (4 * 2 ^ ((d : ℝ) + 3)) * b * ‖z‖ * sb1w ((d : ℝ) + 3) x := by
          have : b * (2 ^ ((d : ℝ) + 3) * sb1w ((d : ℝ) + 3) x) * 1 ≤ b * (2 ^ ((d : ℝ) + 3) * sb1w ((d : ℝ) + 3) x) * (4 * ‖z‖) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          nlinarith

theorem sb1_nsup_integrable (hd : 1 ≤ d) {s : ℝ} (hsd : s < d) {r : ℝ} (hr : r ≤ 1) :
    IntegrableOn (fun z : Euc d => ‖z‖ ^ (-s)) (Metric.closedBall (0 : Euc d) r) := by
  have hdim : 1 ≤ Module.finrank ℝ (Euc d) := by simpa using hd
  have h1 : IntegrableOn (fun z : Euc d => ‖z‖ ^ (-s)) (Metric.ball 0 2) := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) hdim (C := 1) (α := s) (r := 2)
      (by simpa using hsd) ?_ ?_
    · refine ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet fun z _ => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _), one_mul]
    · exact (measurable_norm.pow_const _).aestronglyMeasurable
  refine h1.mono_set ?_
  intro z hz
  simp only [Metric.mem_closedBall, dist_zero_right] at hz
  simp only [Metric.mem_ball, dist_zero_right]
  linarith

/-- **the master estimate** -/
theorem sb1_rgT_diff (hd : 1 ≤ d) {s σ1 σ2 : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {κ1 κ2 : Euc d → ℝ}
    (hκ1 : RgKer d s σ1 κ1) (hκ2 : RgKer d s σ2 κ2) {r : ℝ} (hr1 : r ≤ 1)
    (hsupp : ∀ z : Euc d, r < ‖z‖ → κ1 z = κ2 z) {φ : Euc d → ℝ} (hφd : Differentiable ℝ φ) {b : ℝ}
    (h0 : ∀ y, |φ y| ≤ b * sb1w ((d : ℝ) + 3) y) (h1 : ∀ y, ‖fderiv ℝ φ y‖ ≤ b * sb1w ((d : ℝ) + 3) y) (x : Euc d) :
    |rgT κ1 φ x - rgT κ2 φ x| ≤
      (σ1 + σ2) * ((4 * 2 ^ ((d : ℝ) + 3)) * b * sb1w ((d : ℝ) + 3) x) * sb1eta d s r := by
  have hb : 0 ≤ b := by
    have := (abs_nonneg (φ 0)).trans (h0 0)
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos hneg (sb1w_pos ((d : ℝ) + 3) (0 : Euc d))
    linarith
  have hp : (0 : ℝ) ≤ (d : ℝ) + 3 := by positivity
  have h0' : ∀ y, ‖φ y‖ ≤ b * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := fun y => by
    rw [Real.norm_eq_abs]
    refine (h0 y).trans (mul_le_mul_of_nonneg_left ?_ hb)
    have := sb1w_anti (d := d) (p := (d : ℝ) + 1) (q := (d : ℝ) + 3) (by linarith) (by positivity) y
    simpa [sb1w] using this
  have h1' : ∀ y, ‖fderiv ℝ φ y‖ ≤ b := fun y =>
    (h1 y).trans (mul_le_of_le_one_right hb (sb1w_le_one hp y))
  have i1 := rg_integrable hd hs0 hsd hκ1 hφd hb hb h0' h1' x
  have i2 := rg_integrable hd hs0 hsd hκ2 hφd hb hb h0' h1' x
  unfold rgT
  rw [← integral_sub i1 i2]
  set C : ℝ := (4 * 2 ^ ((d : ℝ) + 3)) * b * sb1w ((d : ℝ) + 3) x with hC
  have hC0 : 0 ≤ C := mul_nonneg (mul_nonneg (by positivity) hb) (sb1w_pos _ _).le
  have hσ1 := hκ1.sigma_nonneg
  have hσ2 := hκ2.sigma_nonneg
  have hint : Integrable (Set.indicator (Metric.closedBall (0 : Euc d) r)
      (fun z : Euc d => ((σ1 + σ2) * C) * ‖z‖ ^ (-s))) := by
    rw [integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
    exact (sb1_nsup_integrable hd hsd hr1).const_mul _
  have hbd : ∀ᵐ z : Euc d ∂volume, ‖κ1 z • rgR φ x z - κ2 z • rgR φ x z‖ ≤
      Set.indicator (Metric.closedBall (0 : Euc d) r) (fun z : Euc d => ((σ1 + σ2) * C) * ‖z‖ ^ (-s)) z := by
    filter_upwards [movtr_ae_ne_zero (d := d) hd] with z hz
    by_cases hzr : r < ‖z‖
    · have hnm : z ∉ Metric.closedBall (0 : Euc d) r := by simpa using hzr
      rw [Set.indicator_of_notMem hnm, hsupp z hzr, sub_self, norm_zero]
    · push Not at hzr
      have hm : z ∈ Metric.closedBall (0 : Euc d) r := by simpa using hzr
      rw [Set.indicator_of_mem hm, ← sub_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hzp : 0 < ‖z‖ := norm_pos_iff.2 hz
      have hk : |κ1 z - κ2 z| ≤ (σ1 + σ2) * ‖z‖ ^ (-s - 1) :=
        (abs_sub _ _).trans (by have := hκ1.bound z hz; have := hκ2.bound z hz; linarith)
      have hR := sb1_rgR_bound hφd h0 h1 x z (hzr.trans hr1)
      have e : ‖z‖ ^ (-s - 1) * ‖z‖ = ‖z‖ ^ (-s) := by
        rw [← Real.rpow_add_one hzp.ne']; congr 1; ring
      calc |κ1 z - κ2 z| * |rgR φ x z| ≤ ((σ1 + σ2) * ‖z‖ ^ (-s - 1)) * (C * ‖z‖) := by
            refine mul_le_mul hk ?_ (abs_nonneg _) (mul_nonneg (add_nonneg hσ1 hσ2) (Real.rpow_nonneg (norm_nonneg _) _))
            calc |rgR φ x z| ≤ (4 * 2 ^ ((d : ℝ) + 3)) * b * ‖z‖ * sb1w ((d : ℝ) + 3) x := hR
              _ = C * ‖z‖ := by rw [hC]; ring
        _ = ((σ1 + σ2) * C) * (‖z‖ ^ (-s - 1) * ‖z‖) := by ring
        _ = ((σ1 + σ2) * C) * ‖z‖ ^ (-s) := by rw [e]
  have := norm_integral_le_of_norm_le hint hbd
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  rw [integral_indicator Metric.isClosed_closedBall.measurableSet, integral_const_mul]
  unfold sb1eta
  ring

end HRS.MS.MfeConf
