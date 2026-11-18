import HRS.MS.S82P2Cent3

/-!
# S8.2 (S82P2): near-diagonal integral of the difference quotient
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

/-- the small-ball constant. -/
def s82p2_ballB (d : ℕ) (G r : ℝ) : ℝ :=
  G * ((d : ℝ) * (volume : Measure (Euc d)).real (Metric.ball (0 : Euc d) 1) *
    (r ^ d / d + r ^ (criticalS d + 1) / (criticalS d + 1)))

lemma s82p2_near_bound {d : ℕ} (hd : 2 ≤ d) {a beta M A : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A)
    (G c : ℝ) (hG : 0 < G) (hc : 0 < c) {rho : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity rho) (hρG : HRS.Whole.HasR2GaussianUpper G c rho)
    {f : Euc d → ℝ} {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q)
    (x v : Euc d) (hv : ‖v‖ = 1) {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1 / 8) :
    ∫⁻ z in Metric.ball x (2 * t), ENNReal.ofReal |t⁻¹ * (Q (x + t • v) z - Q x z)|
        ∂HRS.Whole.withDensityReal rho ≤
      ENNReal.ofReal (t⁻¹ * (2 * A * ((2 * jbracket x) ^ M * (2 * jbracket x) ^ M)) *
        (s82p2_ballB d G (2 * t) + s82p2_ballB d G (3 * t))) := by
  set mu := HRS.Whole.withDensityReal rho with hmu
  set y : Euc d := x + t • v with hy
  have hyx : ‖y - x‖ = t := by
    rw [hy, add_sub_cancel_left, norm_smul, hv, mul_one, Real.norm_eq_abs, abs_of_pos ht0]
  set K1 : ℝ := 2 * A * ((2 * jbracket x) ^ M * (2 * jbracket x) ^ M) with hK1
  have hK10 : 0 ≤ K1 := by
    have := Real.rpow_nonneg (by have := HRS.MS.S82N.s82n_jb_pos x; linarith : 0 ≤ 2 * jbracket x) M
    rw [hK1]; positivity
  have hAm : MeasurableSet (Metric.ball x (2 * t)) := Metric.isOpen_ball.measurableSet
  have hne : ∀ w : Euc d, ∀ᵐ z ∂mu, z ≠ w := fun w => by
    rw [ae_iff]
    simpa using s82p2_mu_singleton hd rho w
  have hae : ∀ᵐ z ∂mu, z ≠ x ∧ z ≠ y := (hne x).and (hne y)
  have he0 : ∀ w z : Euc d, 0 ≤ 1 + ‖w - z‖ ^ (1 - criticalS d) := fun w z => by
    have := Real.rpow_nonneg (norm_nonneg (w - z)) (1 - criticalS d); linarith
  have hmeas : ∀ w : Euc d, Measurable (fun z : Euc d => ENNReal.ofReal (1 + ‖w - z‖ ^ (1 - criticalS d))) :=
    fun w => ENNReal.measurable_ofReal.comp
      (measurable_const.add (((measurable_const.sub measurable_id).norm).pow_const _))
  have hpt : ∀ᵐ z ∂(mu.restrict (Metric.ball x (2 * t))),
      ENNReal.ofReal |t⁻¹ * (Q y z - Q x z)| ≤ ENNReal.ofReal (t⁻¹ * K1) *
        (ENNReal.ofReal (1 + ‖x - z‖ ^ (1 - criticalS d)) +
          ENNReal.ofReal (1 + ‖y - z‖ ^ (1 - criticalS d))) := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hAm] with z hz hzb
    have hzb' : ‖z - x‖ < 2 * t := by
      rw [Metric.mem_ball, dist_eq_norm] at hzb; exact hzb
    have h1 := s82p2_Q_near hd hM hA hQ x x z ht1 (by simp; exact ht0.le) hzb' (Ne.symm hz.1)
    have h2 := s82p2_Q_near hd hM hA hQ x y z ht1 hyx.le hzb' (Ne.symm hz.2)
    rw [← ENNReal.ofReal_add (he0 x z) (he0 y z), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [abs_mul, abs_of_pos (inv_pos.2 ht0)]
    have h3 : |Q y z - Q x z| ≤ |Q y z| + |Q x z| := abs_sub _ _
    calc t⁻¹ * |Q y z - Q x z| ≤ t⁻¹ * (K1 * (1 + ‖y - z‖ ^ (1 - criticalS d)) +
            K1 * (1 + ‖x - z‖ ^ (1 - criticalS d))) := by
          apply mul_le_mul_of_nonneg_left _ (inv_pos.2 ht0).le
          linarith
      _ = t⁻¹ * K1 * (1 + ‖x - z‖ ^ (1 - criticalS d) + (1 + ‖y - z‖ ^ (1 - criticalS d))) := by ring
  calc ∫⁻ z in Metric.ball x (2 * t), ENNReal.ofReal |t⁻¹ * (Q y z - Q x z)| ∂mu
      ≤ ∫⁻ z in Metric.ball x (2 * t), ENNReal.ofReal (t⁻¹ * K1) *
        (ENNReal.ofReal (1 + ‖x - z‖ ^ (1 - criticalS d)) +
          ENNReal.ofReal (1 + ‖y - z‖ ^ (1 - criticalS d))) ∂mu := lintegral_mono_ae hpt
    _ = ENNReal.ofReal (t⁻¹ * K1) * (∫⁻ z in Metric.ball x (2 * t),
          ENNReal.ofReal (1 + ‖x - z‖ ^ (1 - criticalS d)) ∂mu +
        ∫⁻ z in Metric.ball x (2 * t), ENNReal.ofReal (1 + ‖y - z‖ ^ (1 - criticalS d)) ∂mu) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left (hmeas x)]
    _ ≤ ENNReal.ofReal (t⁻¹ * K1) * (ENNReal.ofReal (s82p2_ballB d G (2 * t)) +
          ENNReal.ofReal (s82p2_ballB d G (3 * t))) := by
        gcongr
        · exact s82p2_ball_integral hd G c hG hc rho hρ hρG x (2 * t) (by positivity)
        · refine le_trans (lintegral_mono_set ?_) (s82p2_ball_integral hd G c hG hc rho hρ hρG y
            (3 * t) (by positivity))
          intro z hz
          rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
          have : ‖z - y‖ ≤ ‖z - x‖ + ‖x - y‖ := by simpa using norm_sub_le_norm_sub_add_norm_sub z x y
          rw [norm_sub_rev x y, hyx] at this
          linarith
    _ = ENNReal.ofReal (t⁻¹ * K1 * (s82p2_ballB d G (2 * t) + s82p2_ballB d G (3 * t))) := by
        have hB0 : ∀ r : ℝ, 0 ≤ r → 0 ≤ s82p2_ballB d G r := fun r hr => by
          unfold s82p2_ballB
          have hs0 : 0 < criticalS d := by
            unfold criticalS
            have : (2 : ℝ) ≤ d := by exact_mod_cast hd
            linarith
          have : 0 ≤ (volume : Measure (Euc d)).real (Metric.ball (0 : Euc d) 1) := measureReal_nonneg
          positivity
        rw [← ENNReal.ofReal_add (hB0 _ (by positivity)) (hB0 _ (by positivity)),
          ← ENNReal.ofReal_mul (by positivity)]

end HRS.MS.S82P2
