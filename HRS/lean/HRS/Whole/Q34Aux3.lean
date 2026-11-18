import HRS.Whole.Q34Aux2

/-!
# Packet Q34, helper file 3: the truncated kernel
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace HRS.Whole.Q34

variable {d : ℕ}

/-- The truncation radius `r = H^{-1/s}`. -/
theorem trunc_radius_facts {s H : ℝ} (hs0 : 0 < s) (hH : 1 ≤ H) :
    0 < H ^ (-(1 / s)) ∧ (H ^ (-(1 / s))) ^ (-s) = H := by
  have hH0 : 0 < H := by linarith
  refine ⟨Real.rpow_pos_of_pos hH0 _, ?_⟩
  rw [← Real.rpow_mul hH0.le]
  have : -(1 / s) * -s = 1 := by field_simp
  rw [this, Real.rpow_one]

theorem trunc_sq_le (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hds : (d : ℝ) < 2 * s)
    {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) {H : ℝ} (hH : 1 ≤ H)
    (y : Euc d) :
    ∫⁻ z, ENNReal.ofReal ((min (‖y - z‖ ^ (-s)) H) ^ 2) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal (M * sphereArea d * (1 / (d : ℝ) + 1 / (2 * s - d)) * H ^ (2 - (d : ℝ) / s)) := by
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  have hH0 : 0 < H := by linarith
  obtain ⟨hr0, hrH⟩ := trunc_radius_facts hs0 hH
  set r : ℝ := H ^ (-(1 / s)) with hr
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hsA := sphereArea_nonneg hd
  set H1 : Euc d → ℝ≥0∞ := (ball (0 : Euc d) r).indicator (fun _ => ENNReal.ofReal (H ^ 2))
    with hH1
  set H2 : Euc d → ℝ≥0∞ := {z : Euc d | r ≤ ‖z‖}.indicator
    (fun w => ENNReal.ofReal (‖w‖ ^ (-(2 * s)))) with hH2
  have hH1m : Measurable H1 := measurable_const.indicator measurableSet_ball
  have hH2m : Measurable H2 :=
    (Measurable.ennreal_ofReal (measurable_norm.pow_const _)).indicator
      (measurableSet_le measurable_const measurable_norm)
  have hpt : ∀ w : Euc d, ENNReal.ofReal ((min (‖w‖ ^ (-s)) H) ^ 2) ≤ H1 w + H2 w := by
    intro w
    by_cases hw : ‖w‖ < r
    · have hwb : w ∈ ball (0 : Euc d) r := by simpa using hw
      have : (min (‖w‖ ^ (-s)) H) ^ 2 ≤ H ^ 2 := by
        have h0 : 0 ≤ min (‖w‖ ^ (-s)) H := le_min (Real.rpow_nonneg (norm_nonneg _) _) hH0.le
        exact pow_le_pow_left₀ h0 (min_le_right _ _) 2
      calc ENNReal.ofReal ((min (‖w‖ ^ (-s)) H) ^ 2) ≤ ENNReal.ofReal (H ^ 2) :=
            ENNReal.ofReal_le_ofReal this
        _ = H1 w := by simp [hH1, hwb]
        _ ≤ H1 w + H2 w := le_self_add
    · have hw' : r ≤ ‖w‖ := not_lt.1 hw
      have hmem : w ∈ {z : Euc d | r ≤ ‖z‖} := hw'
      have : (min (‖w‖ ^ (-s)) H) ^ 2 ≤ ‖w‖ ^ (-(2 * s)) := by
        have h0 : 0 ≤ min (‖w‖ ^ (-s)) H := le_min (Real.rpow_nonneg (norm_nonneg _) _) hH0.le
        calc (min (‖w‖ ^ (-s)) H) ^ 2 ≤ (‖w‖ ^ (-s)) ^ 2 :=
              pow_le_pow_left₀ h0 (min_le_left _ _) 2
          _ = ‖w‖ ^ (-(2 * s)) := by
              rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
              congr 1; push_cast; ring
      calc ENNReal.ofReal ((min (‖w‖ ^ (-s)) H) ^ 2) ≤ ENNReal.ofReal (‖w‖ ^ (-(2 * s))) :=
            ENNReal.ofReal_le_ofReal this
        _ = H2 w := by simp [hH2, hmem]
        _ ≤ H1 w + H2 w := le_add_self
  have hpt' : ∀ z : Euc d, ENNReal.ofReal ((min (‖y - z‖ ^ (-s)) H) ^ 2) ≤ (H1 + H2) (y - z) :=
    fun z => hpt (y - z)
  calc ∫⁻ z, ENNReal.ofReal ((min (‖y - z‖ ^ (-s)) H) ^ 2) ∂(withDensityReal ρ)
      ≤ ∫⁻ z, (H1 + H2) (y - z) ∂(withDensityReal ρ) := lintegral_mono hpt'
    _ ≤ ENNReal.ofReal M * ∫⁻ w, (H1 + H2) w :=
        lintegral_conv_le hρ hM _ (hH1m.add hH2m) y
    _ = ENNReal.ofReal (M * sphereArea d * (1 / (d : ℝ) + 1 / (2 * s - d)) *
          H ^ (2 - (d : ℝ) / s)) := by
        have e1 : ∫⁻ w, H1 w = ENNReal.ofReal (H ^ 2 * (sphereArea d * (r ^ d / d))) := by
          rw [hH1, lintegral_indicator measurableSet_ball, lintegral_const,
            Measure.restrict_apply MeasurableSet.univ, univ_inter, volume_ball_eq hd hr0,
            ← ENNReal.ofReal_mul (by positivity)]
        have e2 : ∫⁻ w, H2 w = ENNReal.ofReal (sphereArea d *
            (r ^ ((d : ℝ) - 2 * s) / (2 * s - (d : ℝ)))) := by
          rw [hH2, lintegral_indicator (measurableSet_le measurable_const measurable_norm),
            lintegral_compl_rpow hd hr0 hds]
        have e3 : ∫⁻ w, (H1 + H2) w = ENNReal.ofReal (sphereArea d * (1 / (d : ℝ) + 1 / (2 * s - d)) *
            H ^ (2 - (d : ℝ) / s)) := by
          have hadd : ∫⁻ w, (H1 + H2) w = (∫⁻ w, H1 w) + ∫⁻ w, H2 w :=
            by simpa only [Pi.add_apply] using lintegral_add_left hH1m H2
          rw [hadd, e1, e2]
          have hr1 : r ^ d = H ^ (-((d : ℝ) / s)) := by
            rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hH0.le]
            congr 1; ring
          have hr2 : r ^ ((d : ℝ) - 2 * s) = H ^ (2 - (d : ℝ) / s) := by
            rw [hr, ← Real.rpow_mul hH0.le]
            congr 1; field_simp; ring
          have hH2' : H ^ 2 * H ^ (-((d : ℝ) / s)) = H ^ (2 - (d : ℝ) / s) := by
            rw [← Real.rpow_natCast, ← Real.rpow_add hH0]
            congr 1
          have hpos2 : 0 < 2 * s - (d : ℝ) := by linarith
          rw [← ENNReal.ofReal_add (by positivity) (by
            have := Real.rpow_nonneg (hr0.le) ((d : ℝ) - 2 * s)
            positivity)]
          congr 1
          rw [hr1, hr2]
          have : H ^ 2 * (sphereArea d * (H ^ (-((d : ℝ) / s)) / d)) =
              sphereArea d * (1 / (d : ℝ)) * (H ^ 2 * H ^ (-((d : ℝ) / s))) := by ring
          rw [this, hH2']
          ring
        rw [e3, ← ENNReal.ofReal_mul hM0]
        congr 1
        ring


theorem trunc_diff_le (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d)
    {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) {H : ℝ} (hH : 1 ≤ H)
    (y : Euc d) :
    ∫⁻ z, ENNReal.ofReal (‖y - z‖ ^ (-s) - min (‖y - z‖ ^ (-s)) H) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal (M * sphereArea d / ((d : ℝ) - s) * H ^ (1 - (d : ℝ) / s)) := by
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  have hH0 : 0 < H := by linarith
  obtain ⟨hr0, hrH⟩ := trunc_radius_facts hs0 hH
  set r : ℝ := H ^ (-(1 / s)) with hr
  have hsA := sphereArea_nonneg hd
  have hdm : 0 < (d : ℝ) - s := by linarith
  set H1 : Euc d → ℝ≥0∞ := (ball (0 : Euc d) r).indicator (fun w => ENNReal.ofReal (‖w‖ ^ (-s)))
    with hH1
  have hH1m : Measurable H1 :=
    (Measurable.ennreal_ofReal (measurable_norm.pow_const _)).indicator measurableSet_ball
  have hpt : ∀ w : Euc d, ENNReal.ofReal (‖w‖ ^ (-s) - min (‖w‖ ^ (-s)) H) ≤ H1 w := by
    intro w
    by_cases hw : ‖w‖ < r
    · have hwb : w ∈ ball (0 : Euc d) r := by simpa using hw
      have h0 : 0 ≤ min (‖w‖ ^ (-s)) H := le_min (Real.rpow_nonneg (norm_nonneg _) _) hH0.le
      have : ‖w‖ ^ (-s) - min (‖w‖ ^ (-s)) H ≤ ‖w‖ ^ (-s) := by linarith
      calc ENNReal.ofReal (‖w‖ ^ (-s) - min (‖w‖ ^ (-s)) H) ≤ ENNReal.ofReal (‖w‖ ^ (-s)) :=
            ENNReal.ofReal_le_ofReal this
        _ = H1 w := by simp [hH1, hwb]
    · have hw' : r ≤ ‖w‖ := not_lt.1 hw
      have : ‖w‖ ^ (-s) ≤ H := by
        rw [← hrH]
        exact Real.rpow_le_rpow_of_nonpos hr0 hw' (by linarith)
      rw [min_eq_left this, sub_self]
      simp
  have hpt' : ∀ z : Euc d, ENNReal.ofReal (‖y - z‖ ^ (-s) - min (‖y - z‖ ^ (-s)) H) ≤ H1 (y - z) :=
    fun z => hpt (y - z)
  calc ∫⁻ z, ENNReal.ofReal (‖y - z‖ ^ (-s) - min (‖y - z‖ ^ (-s)) H) ∂(withDensityReal ρ)
      ≤ ∫⁻ z, H1 (y - z) ∂(withDensityReal ρ) := lintegral_mono hpt'
    _ ≤ ENNReal.ofReal M * ∫⁻ w, H1 w := lintegral_conv_le hρ hM _ hH1m y
    _ = ENNReal.ofReal (M * sphereArea d / ((d : ℝ) - s) * H ^ (1 - (d : ℝ) / s)) := by
        have e1 : ∫⁻ w, H1 w = ENNReal.ofReal (sphereArea d *
            (r ^ ((d : ℝ) - s) / ((d : ℝ) - s))) := by
          rw [hH1, lintegral_indicator measurableSet_ball, lintegral_ball_rpow hd hr0 hsd]
        have hr2 : r ^ ((d : ℝ) - s) = H ^ (1 - (d : ℝ) / s) := by
          rw [hr, ← Real.rpow_mul hH0.le]
          congr 1; field_simp; ring
        rw [e1, ← ENNReal.ofReal_mul hM0, hr2]
        congr 1
        ring

end HRS.Whole.Q34
